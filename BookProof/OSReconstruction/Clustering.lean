import Mathlib
import BookProof.OSReconstruction.Hamiltonian

/-!
# Chapter Clustering — Euclidean exponential decay, `O(4)` invariance and the mass

Plan: `cftproof.md`, Phase 5.  With the reflective Euclidean theory reconstructed
(`OSReconstruction.PhysicalSpace`), the mass gap of the emergent Hamiltonian is read off the
**Euclidean clustering** of the Schwinger functions: for observables `F, G` supported in the
positive half-space,

`|⟨θ(F) T_τ G⟩ − ⟨F⟩⟨G⟩| ≤ C e^{−m τ}`,

and, because the measure is `O(4)`-invariant, exponential decay in the *Euclidean time*
direction is equivalent to exponential decay in the *spatial* direction at the same rate `m`.

## Contents

* `schwinger`, `connectedCorr` — the (unconnected and connected) two-point function at
  Euclidean time separation `τ`, evaluated in the OS form;
* `SchwingerClustering ω T m C` — the mass-`m` clustering hypothesis, in the form the plan
  writes it (`C, m` are constants, `m > 0` is the mass);
* **`schwinger_symm`** — for a transfer operator symmetric for the OS form, the correlator at
  time `τ` is the form of the evolved vector against itself:
  `⟨T_τ F, T_τ F⟩ = ⟨T_{2τ} F, F⟩`.  This is the step that turns a *correlator* statement into
  an *operator norm* statement;
* **`osNorm_evol_sq_le_of_clustering`** and **`osNorm_evol_le_of_clustering`** — the
  consequence: off the vacuum, `‖T_τ F‖ ≤ √C e^{−mτ} ‖F‖`.  In other words the Euclidean decay
  bound *is* a contraction bound for the transfer operator, with the same rate, which is the
  sense in which `m` is a mass gap;
* `osNorm_evol_iterate_le` — the rate survives iteration (so `m` is the asymptotic rate, not
  just a one-step bound);
* `cluster_decay_tendsto_zero` — `m > 0` makes the connected correlator vanish at large
  Euclidean time, i.e. the clustering is exponential and not merely bounded;
* **`eNorm_timePoint_eq_spacePoint`** and **`spatial_decay_of_temporal`** — the `O(4)`
  argument of the plan: the swap of the time axis with a space axis is in `O(4)`, so a
  correlator depending only on the Euclidean norm has the same value at `(τ, 0, 0, 0)` and at
  `(0, τ, 0, 0)`, hence temporal decay at rate `m` implies spatial decay at rate `m`;
* `osBilin_le_mul_osNorm`, `osNorm_sub_le` — Cauchy–Schwarz and the reverse triangle
  inequality for the OS seminorm;
* **`osNorm_sub_evol_ge`** — the norm bound **is** a separation: at fixed `τ`,
  `‖(I − T_τ) F‖ ≥ (1 − √C e^{−mτ}) ‖F‖` off the vacuum;
* `genForm` — the effective generator form `(‖F‖² − ⟨F, T_τ F⟩)/τ` of one Euclidean step;
* `one_sub_exp_neg_ge` — `1 − e^{−x} ≥ x/(1 + x)`, the elementary estimate behind the `τ → 0`
  limit;
* **`genForm_ge_of_contraction`** and **`genForm_gap_of_clustering`** — for every `ε ∈ (0,1)`
  there is `τ > 0` with `m(1 − ε)‖F‖² ≤ (‖F‖² − ⟨F, T_τ F⟩)/τ`: the clustering rate `m` is the
  bottom of the *generator's* form spectrum off the vacuum, which is the `SpectralSeparation`
  hypothesis of the Temple/SIRK chain in bounded form;
* §6, the Källén–Lehmann step in the other direction: `klCorr w lam τ = ∑' k, w k e^{−τ lam k}` is
  the two-point function of an atomic spectral measure; **`klCorr_decay_of_gap`** says masses above
  `m` decay it at rate `m` with the *sharp* constant `∑' w`, **`le_mass_of_klCorr_decay`** says
  conversely that decay at rate `m` forces every positively weighted mass to be at least `m` — so
  the rate *is* the bottom of the mass spectrum — and **`schwingerClustering_of_kl`** turns such a
  representation of every connected correlator into `SchwingerClustering ω T m C`.  The clustering
  hypothesis of §1 is then a consequence of the gap, not an independent input;
* §7, the same two implications **without atomicity**: for an arbitrary finite Borel measure `ρ`
  on `ℝ`, `laplace ρ τ = ∫ e^{−τλ} dρ(λ)` decays at rate `m` whenever `ρ` vanishes below `m`
  (`laplace_le_of_massGap`), and an exponential bound at rate `m` forces `ρ` to vanish on `[0, m)`
  (`measure_Iio_eq_zero_of_laplace_decay`) — so the rate is the bottom of the *support* of a general
  spectral measure.  `laplace_map_withDensity` gives the representation itself in a multiplication
  model: `ρ = (μ.withDensity w).map f` has Laplace transform `∫ w x e^{−τ f x} ∂μ`, which is the
  measurable functional calculus `e^{−τM_f} = M_{e^{−τ f}}` read as a KL representation.

## Honest boundary

The exponential clustering hypothesis is **not** proved: it is the Euclidean mass-gap input
(Bałaban's infrared analysis / the cluster expansion), and `cftproof.md` lists it as the open
analytic content of Phase 5.  What is proved here is the *equivalence machinery*: clustering
⇔ decay of the transfer operator off the vacuum, temporal ⇔ spatial decay under `O(4)`
invariance, and the Källén–Lehmann direction of §6 — the rate is the bottom of the mass spectrum,
and a gap in the masses gives clustering.

The Källén–Lehmann step of §6 is stated for **atomic** spectral measures, which is what the diagonal
models of this repository produce (`BookProof.YangMillsFormClosureNonDiagonal` §20–§22: the
spectrum is the closure of a symbol's range on an `ℓ²` basis); §7 removes that restriction and
proves the gap ⇔ decay equivalence for an arbitrary finite Borel measure, and gives the
representation in a multiplication model — the shape `ChapterSpectralMultiplication` produces for a
normal bounded operator with a cyclic vector, with `e^{−τ f}` as the measurable functional calculus.
What remains not claimed is the *generator*: identifying the physical spectral measure `dρ(λ)` with
such a model needs `H_phys` and the strong continuity of the transfer semigroup, which
`OSReconstruction.Hamiltonian` records as unbuilt; and the bounded separation proved in §4 is not
identified with a `SpectralSeparation` of the *unbounded* `H_phys` itself (needs the generator).
The spectral theorem itself is **not** missing:
`BookProof.ChapterSpectralMultiplication` / `ChapterSpectralDirectSum` give it for bounded normal
operators, `ChapterUnboundedSpectralModel` for unbounded self-adjoint ones (Cayley route),
`ChapterStoneConverse` gives the generator of a unitary group, and `physlib/` carries the same
theorem (`SelfAdjointSpectralTheorem.lean`, `CayleySpectralData/SpecTheorem.lean`).  On the bounded
side this file's output is consumed by `BookProof.TempleContinuumGap`, which turns a separation
into a quantitative gap and carries it across an operator-norm limit.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter Topology

noncomputable section

/-! ## 1. The Euclidean two-point functions -/

/-- The **Schwinger two-point function**: `F` evolved to Euclidean time `τ`, paired with `G` at
time `0`. -/
def schwinger (ω : LinearFunctional) (T : TimeTranslation) (F G : Observable) (τ : ℝ) : ℝ :=
  osBilin ω (T τ F) G

/-- The **connected** two-point function: the product of the one-point functions subtracted. -/
def connectedCorr (ω : LinearFunctional) (T : TimeTranslation) (F G : Observable) (τ : ℝ) : ℝ :=
  schwinger ω T F G τ - ω.toFun F * ω.toFun G

/-- **Exponential clustering at mass `m`.**  Every connected two-point function decays at least
as fast as `C e^{−m τ}` in the Euclidean time separation, measured in the OS norms of the
time-zero observables. -/
def SchwingerClustering (ω : LinearFunctional) (T : TimeTranslation) (m C : ℝ) : Prop :=
  ∀ (F G : Observable) (τ : ℝ), 0 ≤ τ →
    |connectedCorr ω T F G τ| ≤ C * Real.exp (-(m * τ)) * osNorm ω F * osNorm ω G

/-- **Symmetry of the transfer operator for the OS form**: `⟨T_τ F, G⟩ = ⟨F, T_τ G⟩`.  This is
the statement that the transfer matrix is self-adjoint with respect to the physical inner
product, and it is what lets a correlator be read as a norm. -/
def TransferSymmetric (ω : LinearFunctional) (T : TimeTranslation) : Prop :=
  ∀ (τ : ℝ) (F G : Observable), osBilin ω (T τ F) G = osBilin ω F (T τ G)

/-! ## 2. From a correlator to an operator norm -/

/-- For a centred observable the connected correlator is the bare one. -/
theorem connectedCorr_eq_schwinger_of_centred {ω : LinearFunctional} {T : TimeTranslation}
    {F G : Observable} {τ : ℝ} (hF : ω.toFun F = 0) :
    connectedCorr ω T F G τ = schwinger ω T F G τ := by
  unfold connectedCorr
  rw [hF]
  ring

/-- **The correlator at time `τ` is the twice-evolved form**: for a symmetric transfer operator,

`⟨T_τ F, T_τ F⟩ = ⟨T_{2τ} F, F⟩`.

The left side is `‖T_τ F‖²` in the OS seminorm, the right side is the Schwinger function at
separation `2τ` — so a bound on the Schwinger function is a bound on the transfer operator. -/
theorem schwinger_symm {ω : LinearFunctional} {T : TimeTranslation}
    (hsymm : TransferSymmetric ω T) (τ : ℝ) (F : Observable) :
    osBilin ω (T τ F) (T τ F) = osBilin ω (T (2 * τ) F) F := by
  rw [hsymm τ F (T τ F), ← timeTranslation_semigroup T τ τ]
  rw [show τ + τ = 2 * τ from by ring]
  exact (osForm_symm' ω (T (2 * τ) F) F).symm

/-- **Clustering gives a contraction of the transfer operator, squared.**  Off the vacuum, the
time-`τ` image of a centred observable has OS norm at most `√C e^{−mτ}` times its own norm:
the Euclidean decay rate *is* the operator decay rate. -/
theorem osNorm_evol_sq_le_of_clustering {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m C : ℝ}
    (hcl : SchwingerClustering ω T m C) (hsymm : TransferSymmetric ω T)
    {F : Observable} (hF : ω.toFun F = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    osNorm ω (T τ F) ^ 2 ≤ C * Real.exp (-(m * (2 * τ))) * (osNorm ω F) ^ 2 := by
  rw [osNorm_sq ω hRP (T τ F), schwinger_symm hsymm τ F]
  have h := hcl F F (2 * τ) (by linarith)
  rw [connectedCorr_eq_schwinger_of_centred hF] at h
  have hupper : osBilin ω (T (2 * τ) F) F ≤ C * Real.exp (-(m * (2 * τ))) * osNorm ω F *
      osNorm ω F := (abs_le.mp h).2
  have hnn : 0 ≤ Real.exp (-(m * (2 * τ))) := Real.exp_nonneg _
  calc osBilin ω (T (2 * τ) F) F ≤ C * Real.exp (-(m * (2 * τ))) * osNorm ω F * osNorm ω F := hupper
    _ = C * Real.exp (-(m * (2 * τ))) * (osNorm ω F) ^ 2 := by ring

/-- **Clustering gives a contraction**: `‖T_τ F‖ ≤ √C e^{−mτ} ‖F‖` off the vacuum. -/
theorem osNorm_evol_le_of_clustering {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m C : ℝ}
    (hcl : SchwingerClustering ω T m C) (hsymm : TransferSymmetric ω T)
    (hC : 0 ≤ C) {F : Observable} (hF : ω.toFun F = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    osNorm ω (T τ F) ≤ Real.sqrt C * Real.exp (-(m * τ)) * osNorm ω F := by
  set A := Real.sqrt C * Real.exp (-(m * τ)) * osNorm ω F with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    have := osNorm_nonneg ω F
    positivity
  have hA2 : A ^ 2 = C * Real.exp (-(m * (2 * τ))) * (osNorm ω F) ^ 2 := by
    have hexp : Real.exp (-(m * (2 * τ))) = Real.exp (-(m * τ)) ^ 2 := by
      rw [show -(m * (2 * τ)) = -(m * τ) + -(m * τ) from by ring, Real.exp_add, pow_two]
    rw [hA, hexp, mul_pow, mul_pow, Real.sq_sqrt hC]
  have hsq := osNorm_evol_sq_le_of_clustering hRP hcl hsymm hF hτ
  have hle : osNorm ω (T τ F) ^ 2 ≤ A ^ 2 := by rw [hA2]; exact hsq
  have hnn := osNorm_nonneg ω (T τ F)
  nlinarith [hle, hnn, hAnn]

/-- Centred observables stay centred — the hypothesis under which the decay rate iterates. -/
def CentredStable (ω : LinearFunctional) (T : TimeTranslation) : Prop :=
  ∀ (τ : ℝ) (F : Observable), ω.toFun F = 0 → ω.toFun (T τ F) = 0

/-- Iterating the stability hypothesis. -/
theorem centredStable_iterate {ω : LinearFunctional} {T : TimeTranslation}
    (hcent : CentredStable ω T) {F : Observable} (hF : ω.toFun F = 0) (τ : ℝ) (n : ℕ) :
    ω.toFun ((T τ)^[n] F) = 0 := by
  induction n with
  | zero => simpa using hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hcent τ _ ih

/-- **The rate is asymptotic**: clustering at mass `m` makes the `n`-fold evolved norm decay
like `(√C e^{−mτ})^n`. -/
theorem osNorm_evol_iterate_le {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m C : ℝ}
    (hcl : SchwingerClustering ω T m C) (hsymm : TransferSymmetric ω T)
    (hcent : CentredStable ω T) (hC : 0 ≤ C) {F : Observable} (hF : ω.toFun F = 0)
    {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    osNorm ω ((T τ)^[n] F) ≤ (Real.sqrt C * Real.exp (-(m * τ))) ^ n * osNorm ω F := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hFn : ω.toFun ((T τ)^[n] F) = 0 := centredStable_iterate hcent hF τ n
    calc osNorm ω ((T τ)^[n + 1] F)
        = osNorm ω (T τ ((T τ)^[n] F)) := by rw [Function.iterate_succ_apply']
      _ ≤ Real.sqrt C * Real.exp (-(m * τ)) * osNorm ω ((T τ)^[n] F) :=
          osNorm_evol_le_of_clustering hRP hcl hsymm hC hFn hτ
      _ ≤ Real.sqrt C * Real.exp (-(m * τ)) *
            ((Real.sqrt C * Real.exp (-(m * τ))) ^ n * osNorm ω F) := by
          have := osNorm_nonneg ω F
          have hexp : 0 ≤ Real.exp (-(m * τ)) := Real.exp_nonneg _
          have hsqrt : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
          exact mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (Real.sqrt C * Real.exp (-(m * τ))) ^ (n + 1) * osNorm ω F := by
          rw [pow_succ]
          ring

/-- **A positive mass kills the correlations**: with `m > 0` the clustering bound tends to zero
in the time separation — the decay is exponential, not merely bounded. -/
theorem cluster_decay_tendsto_zero {C m K : ℝ} (hm : 0 < m) :
    Tendsto (fun τ : ℝ => C * Real.exp (-(m * τ)) * K) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun τ : ℝ => Real.exp (-(m * τ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hm tendsto_id)
  simpa using (hcomp.const_mul C).mul_const K

/-! ## 3. The `O(4)` argument: temporal decay is spatial decay -/

/-- The Euclidean norm on `Fin 4 → ℝ` coordinates, written out so that permutation invariance
(a coordinate swap) is a single `ring` fact. -/
def eNorm (v : Fin 4 → ℝ) : ℝ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2)

/-- The point `(τ, 0, 0, 0)`: a Euclidean time displacement. -/
def timePoint (τ : ℝ) : Fin 4 → ℝ := ![τ, 0, 0, 0]

/-- The point `(0, r, 0, 0)`: a purely spatial displacement. -/
def spacePoint (r : ℝ) : Fin 4 → ℝ := ![0, r, 0, 0]

theorem eNorm_timePoint (τ : ℝ) : eNorm (timePoint τ) = |τ| := by
  unfold eNorm timePoint
  simp
  rw [Real.sqrt_sq_eq_abs]

theorem eNorm_spacePoint (r : ℝ) : eNorm (spacePoint r) = |r| := by
  unfold eNorm spacePoint
  simp
  rw [Real.sqrt_sq_eq_abs]

/-- **The time axis and a space axis are related by an `O(4)` element** — the coordinate swap,
which is an isometry of `eNorm`.  Hence an `O(4)`-invariant correlator takes the same value at
`(τ,0,0,0)` and `(0,τ,0,0)`. -/
theorem eNorm_timePoint_eq_spacePoint (τ : ℝ) : eNorm (timePoint τ) = eNorm (spacePoint τ) := by
  rw [eNorm_timePoint, eNorm_spacePoint]

/-- **Temporal clustering implies spatial clustering.**  If the Euclidean correlator depends
only on the Euclidean norm (`O(4)` invariance, as the hypothesis `hinv` says) and decays
exponentially in Euclidean time at rate `m`, then it decays exponentially in space at the same
rate, for every direction — this is `cftproof.md` Phase 5, item 1. -/
theorem spatial_decay_of_temporal (corr : (Fin 4 → ℝ) → ℝ)
    (hinv : ∀ v w : Fin 4 → ℝ, eNorm v = eNorm w → corr v = corr w)
    {C m : ℝ} (hbound : ∀ τ : ℝ, 0 ≤ τ → corr (timePoint τ) ≤ C * Real.exp (-(m * τ)))
    (r : ℝ) :
    corr (spacePoint r) ≤ C * Real.exp (-(m * |r|)) := by
  have hsame : corr (spacePoint r) = corr (timePoint |r|) :=
    hinv _ _ (by rw [eNorm_spacePoint, eNorm_timePoint, abs_abs])
  rw [hsame]
  exact hbound |r| (abs_nonneg r)

/-! ## 4. From the norm bound to a spectral separation

Clustering gives a contraction of the transfer operator off the vacuum (§2).  That contraction
*is* a spectral separation, in two equivalent readings:

* at fixed Euclidean time `τ`, the operator `I − T_τ` has a **norm gap** `1 − √C e^{−mτ}` —
  `osNorm_sub_evol_ge`.  This is the bounded-operator form of `SpectralSeparation`: no vector
  orthogonal to the vacuum is annihilated by `I − T_τ`;
* after dividing by `τ`, the same inequality is the **form gap** of the effective generator
  `(I − T_τ)/τ`, and as `τ → 0` the gap tends to `m` itself (`genForm_ge_of_contraction`):
  `m` is the bottom of the generator's form spectrum off the vacuum, not merely a rate in a
  two-point function.  This is the `cftproof.md` Phase-5 item (ii) in the only form the corpus
  can state it — the operator `H_phys` itself is not constructed (see
  `OSReconstruction.Hamiltonian`), so the separation is stated for `(I − T_τ)/τ`.
-/

/-- **Cauchy–Schwarz for the OS form**, in norm form: `⟨F, G⟩ ≤ ‖F‖ ‖G‖`. -/
theorem osBilin_le_mul_osNorm (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (F G : Observable) :
    osBilin ω F G ≤ osNorm ω F * osNorm ω G := by
  have hcs := osForm_cauchy_schwarz ω hRP F G
  have ha := osForm_self_nonneg ω hRP F
  have hc := osForm_self_nonneg ω hRP G
  have hunit : |osBilin ω F G| ≤ osNorm ω F * osNorm ω G := by
    have h1 : |osBilin ω F G| = Real.sqrt (osBilin ω F G ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [h1, osNorm, osNorm, ← Real.sqrt_mul ha]
    exact Real.sqrt_le_sqrt hcs
  calc osBilin ω F G ≤ |osBilin ω F G| := le_abs_self _
    _ ≤ osNorm ω F * osNorm ω G := hunit

/-- **Reverse triangle inequality** for the OS seminorm. -/
theorem osNorm_sub_le (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (F G : Observable) :
    osNorm ω F - osNorm ω G ≤ osNorm ω (F - G) := by
  have h := osNorm_triangle ω hRP (F - G) G
  rw [sub_add_cancel] at h
  linarith

/-- **The transfer operator has a norm gap at fixed `τ`.**  Off the vacuum,
`‖(I − T_τ) F‖ ≥ (1 − √C e^{−mτ}) ‖F‖`: a clustering rate `m` *is* a spectral separation for
`I − T_τ`, with no further input. -/
theorem osNorm_sub_evol_ge {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m C : ℝ}
    (hcl : SchwingerClustering ω T m C) (hsymm : TransferSymmetric ω T) (hC : 0 ≤ C)
    {F : Observable} (hF : ω.toFun F = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    (1 - Real.sqrt C * Real.exp (-(m * τ))) * osNorm ω F ≤ osNorm ω (F - T τ F) := by
  have hbound := osNorm_evol_le_of_clustering hRP hcl hsymm hC hF hτ
  have hdecomp : osNorm ω F ≤ osNorm ω (F - T τ F) + osNorm ω (T τ F) := by
    have h := osNorm_triangle ω hRP (F - T τ F) (T τ F)
    rwa [sub_add_cancel] at h
  nlinarith [hbound, hdecomp, osNorm_nonneg ω F]

/-- The **effective generator form** of one Euclidean time step: the energy of `F` under
`(I − T_τ)/τ`, i.e. `(‖F‖² − ⟨F, T_τ F⟩)/τ`. -/
def genForm (ω : LinearFunctional) (T : TimeTranslation) (τ : ℝ) (F : Observable) : ℝ :=
  (osBilin ω F F - osBilin ω F (T τ F)) / τ

/-- **The elementary exponential bound**: `1 − e^{−x} ≥ x/(1 + x)` for `x ≥ 0`. -/
theorem one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hexp : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have h1 : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := (inv_le_inv₀ hexp hpos).mpr h1
  calc x / (1 + x) = 1 - (1 + x)⁻¹ := by
        field_simp
        ring
    _ ≤ 1 - (Real.exp x)⁻¹ := by linarith
    _ = 1 - Real.exp (-x) := by rw [Real.exp_neg]

/-- **The generator gap is at least `m`.**  If the transfer operator contracts at rate
`e^{−mτ}` off the vacuum — the clustering bound in its normalised form — then for every
`ε ∈ (0,1)` there is a time step `τ > 0` for which the effective generator has form gap
`m(1 − ε)`:

`m (1 − ε) ‖F‖² ≤ (‖F‖² − ⟨F, T_τ F⟩)/τ`.

So the exponential rate `m` of the Euclidean two-point function is the bottom of the form
spectrum of the emergent generator, off the vacuum — `cftproof.md` Phase 5, the step from the
norm bound to the separation. -/
theorem genForm_ge_of_contraction {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m : ℝ} (hm : 0 < m)
    (hevol : ∀ (F : Observable) (τ : ℝ), 0 ≤ τ → ω.toFun F = 0 →
      osNorm ω (T τ F) ≤ Real.exp (-(m * τ)) * osNorm ω F)
    {F : Observable} (hF : ω.toFun F = 0) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ τ : ℝ, 0 < τ ∧ m * (1 - ε) * osNorm ω F ^ 2 ≤ genForm ω T τ F := by
  have hpos : (0 : ℝ) < 1 - ε := by linarith
  refine ⟨ε / (m * (1 - ε)), by positivity, ?_⟩
  set τ : ℝ := ε / (m * (1 - ε)) with hτ
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  -- the two-point bound at this `τ`
  have hcontr := hevol F τ hτ0.le hF
  have hcs := osBilin_le_mul_osNorm ω hRP F (T τ F)
  have hnn := osNorm_nonneg ω F
  -- `⟨F, T_τ F⟩ ≤ e^{−mτ} ‖F‖²`
  have hpair : osBilin ω F (T τ F) ≤ Real.exp (-(m * τ)) * osNorm ω F ^ 2 := by
    have hmul : osNorm ω F * osNorm ω (T τ F) ≤
        osNorm ω F * (Real.exp (-(m * τ)) * osNorm ω F) := by
      exact mul_le_mul_of_nonneg_left hcontr hnn
    nlinarith [hcs, hmul]
  -- the exponential estimate at `x = m τ`
  have hx : (0 : ℝ) ≤ m * τ := by positivity
  have hexp := one_sub_exp_neg_ge hx
  have hxval : m * τ = ε / (1 - ε) := by
    rw [hτ]; field_simp
  have hrat : ε ≤ m * τ / (1 + m * τ) := by
    rw [hxval]
    refine le_div_iff₀ (by positivity) |>.mpr ?_
    have : ε + ε * (ε / (1 - ε)) = ε / (1 - ε) := by
      field_simp; ring
    linarith
  -- assemble
  have hnum : (1 - Real.exp (-(m * τ))) * osNorm ω F ^ 2 ≤
      osBilin ω F F - osBilin ω F (T τ F) := by
    have hsq : osBilin ω F F = osNorm ω F ^ 2 := (osNorm_sq ω hRP F).symm
    rw [hsq]
    nlinarith [hpair, hexp, hrat, hnn]
  rw [genForm, le_div_iff₀ hτ0]
  have htau : m * (1 - ε) * τ = ε := by
    rw [hτ]; field_simp
  nlinarith [hnum, hnn, htau, hexp, hrat]

/-- **From clustering to the generator gap.**  `SchwingerClustering` at mass `m` with constant
`C ≤ 1` (the normalised clustering bound) gives the norm contraction hypothesis of
`genForm_ge_of_contraction` with rate `m`, hence the form gap `m(1 − ε)` at a suitable `τ`. -/
theorem genForm_gap_of_clustering {ω : LinearFunctional}
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {T : TimeTranslation} {m C : ℝ}
    (hcl : SchwingerClustering ω T m C) (hsymm : TransferSymmetric ω T) (hC1 : C ≤ 1)
    (hC : 0 ≤ C) (hm : 0 < m) {F : Observable} (hF : ω.toFun F = 0) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ τ : ℝ, 0 < τ ∧ m * (1 - ε) * osNorm ω F ^ 2 ≤ genForm ω T τ F := by
  have hsqrt : Real.sqrt C ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hC1
  refine genForm_ge_of_contraction hRP hm ?_ hF hε0 hε1
  intro G τ hτ hG
  have h := osNorm_evol_le_of_clustering hRP hcl hsymm hC hG hτ
  have hnn := osNorm_nonneg ω G
  have hexp : (0 : ℝ) ≤ Real.exp (-(m * τ)) := Real.exp_nonneg _
  calc osNorm ω (T τ G) ≤ Real.sqrt C * Real.exp (-(m * τ)) * osNorm ω G := h
    _ ≤ 1 * (Real.exp (-(m * τ)) * osNorm ω G) := by
        have : Real.sqrt C * (Real.exp (-(m * τ)) * osNorm ω G) ≤
            1 * (Real.exp (-(m * τ)) * osNorm ω G) :=
          mul_le_mul_of_nonneg_right hsqrt (by positivity)
        nlinarith
    _ = Real.exp (-(m * τ)) * osNorm ω G := one_mul _

/-! ## 6. Källén–Lehmann: the decay rate is the bottom of the mass spectrum

§2–§4 took clustering as input and read a spectral separation off it.  This section supplies the
other direction — the one `cftproof.md` Phase 5 lists as the Källén–Lehmann input: *why* a gap in
the spectrum produces exponential clustering, and *why* the rate is exactly the bottom of the mass
spectrum rather than a number to be fitted.

The Källén–Lehmann representation of a two-point function is a spectral measure `dρ(λ)` integrated
against the Euclidean kernel `e^{−τλ}`.  The diagonal models of this repository — `diagUnb` in
`BookProof.YangMillsFormClosureNonDiagonal`, whose spectrum is the closure of its symbol's range —
have *atomic* spectral measures, so the representation is a weighted sum:

`klCorr w lam τ = ∑' k, w k · e^{−τ lam k}`.

Both directions are proved for that form, and they are exact:

* **`klCorr_decay_of_gap`** — masses bounded below by `m` decay the two-point function at rate `m`
  with the **sharp** constant `∑' w`, with no loss: the constant is the total spectral weight, not a
  norm bound;
* **`le_mass_of_klCorr_decay`** — conversely, decay at rate `m` forces every *mass with positive
  weight* to be at least `m`: a mass below the rate would make the rescaled ratio
  `w k₀ e^{(lam − m)τ}` grow without bound, contradicting the bound.  So the largest admissible rate
  is the bottom of the mass support — the identification `cftproof.md` asks for;
* **`schwingerClustering_of_kl`** — the transfer: a KL representation of every connected
  two-point function, with masses above `m` and total weight bounded by `C ‖F‖ ‖G‖`, *is*
  `SchwingerClustering ω T m C`.  The clustering hypothesis of §1 is therefore not an extra
  assumption when the spectral measure is known; it is a consequence of the gap.

What is still not claimed: the *physical* spectral measure is not atomic, and the measurable
functional calculus that would turn a general `dρ(λ)` into `e^{−τH}` for the emergent Hamiltonian is
not constructed (`OSReconstruction.Hamiltonian` records why: `H_phys` itself is not built).  The
section is therefore the KL step for the diagonal spectral models used in this repository, stated
at that strength.
-/

section KallenLehmann

variable {ι : Type*}

/-- **An atomic Källén–Lehmann two-point function**: the spectral weight `w` over the masses `lam`,
integrated against the Euclidean kernel `e^{−τλ}`. -/
noncomputable def klCorr (w lam : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑' k, w k * Real.exp (-(τ * lam k))

theorem klCorr_nonneg {w lam : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (τ : ℝ) : 0 ≤ klCorr w lam τ :=
  tsum_nonneg fun k => mul_nonneg (hw k) (Real.exp_nonneg _)

/-- The spectral summands are summable as soon as the weight and the masses are, because
`e^{−τλ} ≤ 1` for nonnegative `τ` and `λ`. -/
theorem summable_klCorr {w lam : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hlam0 : ∀ k, 0 ≤ lam k) {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable fun k => w k * Real.exp (-(τ * lam k)) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (Real.exp_nonneg _))
    (fun k => ?_) hws
  have h1 : Real.exp (-(τ * lam k)) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ τ * lam k := mul_nonneg hτ (hlam0 k)
    linarith
  calc w k * Real.exp (-(τ * lam k)) ≤ w k * 1 := mul_le_mul_of_nonneg_left h1 (hw k)
    _ = w k := mul_one _

/-- **A gap in the masses decays the two-point function at the gap's rate**, with the sharp
constant `∑' w`: the spectral weight above the gap is weighted by `e^{−mτ}` and no more. -/
theorem klCorr_decay_of_gap {w lam : ι → ℝ} {m : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hlam0 : ∀ k, 0 ≤ lam k) (hg : ∀ k, m ≤ lam k) (hws : Summable w) {τ : ℝ} (hτ : 0 ≤ τ) :
    klCorr w lam τ ≤ Real.exp (-(m * τ)) * ∑' k, w k := by
  have hexp : ∀ k, Real.exp (-(τ * lam k)) ≤ Real.exp (-(m * τ)) := by
    intro k
    refine Real.exp_le_exp.mpr ?_
    have hle : τ * m ≤ τ * lam k := mul_le_mul_of_nonneg_left (hg k) hτ
    linarith
  have hf : Summable fun k => w k * Real.exp (-(τ * lam k)) := summable_klCorr hw hws hlam0 hτ
  have hsum : Summable fun k => w k * Real.exp (-(m * τ)) := hws.mul_right _
  calc klCorr w lam τ = ∑' k, w k * Real.exp (-(τ * lam k)) := rfl
    _ ≤ ∑' k, w k * Real.exp (-(m * τ)) :=
        hf.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hexp k) (hw k)) hsum
    _ = Real.exp (-(m * τ)) * ∑' k, w k := by rw [tsum_mul_right, mul_comm]

/-- **No mass below the decay rate has positive weight** — the converse of
`klCorr_decay_of_gap`, and the reason the rate *is* the bottom of the spectrum rather than a bound
for it.  A mass `lam k₀ < m` with `w k₀ > 0` makes the rescaled ratio
`w k₀ e^{(lam k₀ − m)τ}` diverge, contradicting any exponential bound. -/
theorem le_mass_of_klCorr_decay {w lam : ι → ℝ} {m C : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hws : Summable w) (hlam0 : ∀ k, 0 ≤ lam k)
    (hbound : ∀ τ : ℝ, 0 ≤ τ → klCorr w lam τ ≤ C * Real.exp (-(m * τ))) {k₀ : ι}
    (hk₀ : 0 < w k₀) : m ≤ lam k₀ := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < m - lam k₀ := by linarith
  -- the rescaled bound tends to zero
  have hlim : Tendsto (fun τ : ℝ => C * Real.exp (τ * (lam k₀ - m))) atTop (𝓝 0) := by
    have harg : Tendsto (fun τ : ℝ => τ * (m - lam k₀)) atTop atTop := by
      have h1 : Tendsto (fun τ : ℝ => (m - lam k₀) * τ) atTop atTop :=
        Tendsto.const_mul_atTop hpos tendsto_id
      exact h1.congr' (Eventually.of_forall fun τ => mul_comm _ _)
    have h2 : Tendsto (fun τ : ℝ => C * Real.exp (-(τ * (m - lam k₀)))) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).const_mul C
      simpa using h
    refine h2.congr' (Eventually.of_forall fun τ => ?_)
    have : -(τ * (m - lam k₀)) = τ * (lam k₀ - m) := by ring
    rw [this]
  obtain ⟨τ, hlt, hτ0⟩ := (hlim.eventually (Iio_mem_nhds hk₀)).and
    (eventually_ge_atTop (0 : ℝ)) |>.exists
  -- the single term is bounded by the whole spectral sum
  have hsm := summable_klCorr hw hws hlam0 hτ0
  have hsingle : w k₀ * Real.exp (-(τ * lam k₀)) ≤ klCorr w lam τ := by
    have h := hsm.sum_le_tsum {k₀} (fun i _ => mul_nonneg (hw i) (Real.exp_nonneg _))
    simpa [klCorr] using h
  have hkey : w k₀ * Real.exp (-(τ * lam k₀)) ≤ C * Real.exp (-(m * τ)) :=
    hsingle.trans (hbound τ hτ0)
  -- divide by the positive kernel value
  have hkpos : 0 < Real.exp (-(τ * lam k₀)) := Real.exp_pos _
  have hdiv : w k₀ ≤ C * Real.exp (τ * (lam k₀ - m)) := by
    have hsplit : w k₀ = (w k₀ * Real.exp (-(τ * lam k₀))) / Real.exp (-(τ * lam k₀)) := by
      field_simp
    rw [hsplit]
    refine (div_le_iff₀ hkpos).mpr ?_
    have hexp : (C * Real.exp (τ * (lam k₀ - m))) * Real.exp (-(τ * lam k₀))
        = C * Real.exp (-(m * τ)) := by
      rw [mul_assoc, ← Real.exp_add, show τ * (lam k₀ - m) + -(τ * lam k₀) = -(m * τ) from by ring]
    rw [hexp]
    exact hkey
  linarith

/-- **Källén–Lehmann implies clustering.**  If every connected two-point function has an atomic KL
representation whose masses are bounded below by `m` and whose total weight is at most
`C ‖F‖ ‖G‖`, then the Schwinger functions cluster at mass `m` with constant `C`.  The clustering
hypothesis of §1 is then a *consequence* of the gap, and the rate needs no fitting. -/
theorem schwingerClustering_of_kl {ω : LinearFunctional} {T : TimeTranslation} {m C : ℝ}
    (w : Observable → Observable → ι → ℝ) (lam : ι → ℝ)
    (hw : ∀ F G k, 0 ≤ w F G k) (hws : ∀ F G, Summable (w F G))
    (hlam0 : ∀ k, 0 ≤ lam k) (hm : ∀ k, m ≤ lam k)
    (hrep : ∀ (F G : Observable) (τ : ℝ), 0 ≤ τ → |connectedCorr ω T F G τ| ≤ klCorr (w F G) lam τ)
    (hC : ∀ F G, (∑' k, w F G k) ≤ C * osNorm ω F * osNorm ω G) :
    SchwingerClustering ω T m C := by
  intro F G τ hτ
  calc |connectedCorr ω T F G τ| ≤ klCorr (w F G) lam τ := hrep F G τ hτ
    _ ≤ Real.exp (-(m * τ)) * ∑' k, w F G k :=
        klCorr_decay_of_gap (hw F G) hlam0 hm (hws F G) hτ
    _ ≤ Real.exp (-(m * τ)) * (C * osNorm ω F * osNorm ω G) :=
        mul_le_mul_of_nonneg_left (hC F G) (Real.exp_nonneg _)
    _ = C * Real.exp (-(m * τ)) * osNorm ω F * osNorm ω G := by ring

end KallenLehmann

/-! ## 7. Källén–Lehmann without atomicity

§6 reads the mass spectrum off an *atomic* spectral measure: a sum over eigenvalues.  The physical
`dρ` is not atomic, and the representation `⟪φ, e^{−τH}φ⟫ = ∫ e^{−τλ} dρ(λ)` is then an integral,
not a series.  This section proves the same two implications for an **arbitrary finite Borel measure
on `ℝ`** — no atomicity anywhere — and then gives the representation itself for the multiplication
model that the repository's spectral theorem produces.

* `laplace` — the Euclidean kernel `∫ e^{−τλ} dρ(λ)` of a measure;
* **`laplace_le_of_massGap`** — if `ρ` vanishes below `m`, the transform decays at rate `m` with
  the constant `ρ(ℝ)`, and no eigenvalue decomposition is used: the kernel is compared with
  `e^{−mτ}` almost everywhere, which is Fatou's-side of the statement and therefore insensitive to
  the measure's atomicity;
* **`measure_Iio_eq_zero_of_laplace_decay`** — conversely, an exponential bound at rate `m` forces
  `ρ` to vanish on `[0, m)`: the rate *is* the bottom of the support of the spectral measure, again
  for any finite measure;
* **`laplace_map_withDensity`** — the representation: for a measure `μ`, a measurable symbol `f` and
  a weight `w`, the pushforward `ρ = (μ.withDensity w).map f` satisfies
  `∫ e^{−τλ} dρ = ∫ w x e^{−τ f x} ∂μ`.  This is the measurable functional calculus
  `e^{−τ M_f} = M_{e^{−τ f}}` read as a KL representation, and `ρ` is atomic only if `f` has
  atomic fibres.

`ChapterSpectralMultiplication` supplies exactly such a model for a normal bounded operator with a
cyclic vector (`spectral_multiplication_model`, `integral_spectralMeasure`), so the KL step applies
to it verbatim; §6 is the case where `μ` is counting measure on the eigenvalues.

What is still not claimed: `H_phys` itself.  Identifying the physical spectral measure with a
multiplication model needs the generator of the transfer semigroup, which
`OSReconstruction.Hamiltonian` records as unbuilt.  What is removed here is the *atomicity* of the
measure, not the construction of the Hamiltonian.
-/

section KallenLehmannGeneral

open MeasureTheory

open scoped ENNReal

/-- The **Laplace transform of a finite measure**: the Euclidean two-point function of a spectral
measure, `∫ e^{−τλ} dρ(λ)`. -/
noncomputable def laplace (ρ : Measure ℝ) (τ : ℝ) : ℝ :=
  ∫ l, Real.exp (-(τ * l)) ∂ρ

theorem laplace_nonneg (ρ : Measure ℝ) (τ : ℝ) : 0 ≤ laplace ρ τ :=
  integral_nonneg fun _ => Real.exp_nonneg _

/-- **A mass gap decays the transform at the gap's rate, for any finite measure.**  If `ρ` has no
mass below `m`, then `e^{−τλ} ≤ e^{−mτ}` `ρ`-almost everywhere, and integrating gives the bound with
the total mass `ρ(ℝ)` as constant.  Nothing here is a sum over eigenvalues. -/
theorem laplace_le_of_massGap {ρ : Measure ℝ} [IsFiniteMeasure ρ] {m τ : ℝ} (hτ : 0 ≤ τ)
    (hint : Integrable (fun l : ℝ => Real.exp (-(τ * l))) ρ) (hsupp : ρ (Set.Iio m) = 0) :
    laplace ρ τ ≤ (ρ Set.univ).toReal * Real.exp (-(m * τ)) := by
  have hsupp' : ρ {l : ℝ | ¬ m ≤ l} = 0 := by
    have hset : {l : ℝ | ¬ m ≤ l} = Set.Iio m := by ext l; simp [not_le]
    rw [hset]
    exact hsupp
  have hmono : (fun l : ℝ => Real.exp (-(τ * l))) ≤ᵐ[ρ] fun _ => Real.exp (-(m * τ)) := by
    filter_upwards [ae_iff.2 hsupp'] with l hl
    have hle : m ≤ l := hl
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hInt : Integrable (fun _ : ℝ => Real.exp (-(m * τ))) ρ := integrable_const _
  have h := integral_mono_ae hint hInt hmono
  rw [integral_const] at h
  simpa only [laplace, Measure.real, smul_eq_mul] using h

/-- **The rate is the bottom of the mass spectrum, for any finite measure.**  If the transform
decays at rate `m`, then `ρ` has no mass on `[0, m)` — in particular none at `0`.  The proof takes a
strictly smaller threshold `m' < m` and lets `τ → ∞`: the mass below `m'` is bounded by
`C e^{−τ(m−m')}`, which vanishes. -/
theorem measure_Iio_eq_zero_of_laplace_decay {ρ : Measure ℝ} [IsFiniteMeasure ρ] {m C : ℝ}
    (hint : ∀ τ : ℝ, 0 ≤ τ → Integrable (fun l : ℝ => Real.exp (-(τ * l))) ρ)
    (hdecay : ∀ τ : ℝ, 0 ≤ τ → laplace ρ τ ≤ C * Real.exp (-(m * τ))) {m' : ℝ} (hm' : m' < m) :
    ρ (Set.Iio m') = 0 := by
  by_contra hne
  have hpos : 0 < ρ (Set.Iio m') := lt_of_le_of_ne (zero_le _) (Ne.symm hne)
  -- the lower bound `e^{−τm'} ρ(Iio m') ≤ laplace ρ τ`
  have hlower : ∀ τ : ℝ, 0 ≤ τ →
      Real.exp (-(τ * m')) * (ρ (Set.Iio m')).toReal ≤ laplace ρ τ := by
    intro τ hτ
    have hInt := hint τ hτ
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp (-(τ * m'))) (Set.Iio m') ρ :=
      integrableOn_const (measure_ne_top _ _)
    have hmono : ∀ l ∈ Set.Iio m', Real.exp (-(τ * m')) ≤ Real.exp (-(τ * l)) := by
      intro l hl
      refine Real.exp_le_exp.2 ?_
      have : τ * l ≤ τ * m' := mul_le_mul_of_nonneg_left (le_of_lt hl) hτ
      linarith
    have hset := setIntegral_mono_on (μ := ρ) (s := Set.Iio m')
      (f := fun _ : ℝ => Real.exp (-(τ * m'))) (g := fun l : ℝ => Real.exp (-(τ * l)))
      hconst hInt.integrableOn measurableSet_Iio hmono
    rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm] at hset
    refine hset.trans ?_
    exact setIntegral_le_integral hInt (Eventually.of_forall fun _ => Real.exp_nonneg _)
  -- divide by the positive kernel value
  have hmass : ∀ τ : ℝ, 0 ≤ τ →
      (ρ (Set.Iio m')).toReal ≤ C * Real.exp (-(τ * (m - m'))) := by
    intro τ hτ
    have hk : 0 < Real.exp (-(τ * m')) := Real.exp_pos _
    have hle := (hlower τ hτ).trans (hdecay τ hτ)
    have hexpfac : Real.exp (-(m * τ))
        = Real.exp (-(τ * m')) * Real.exp (-(τ * (m - m'))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsplit : C * Real.exp (-(m * τ))
        = Real.exp (-(τ * m')) * (C * Real.exp (-(τ * (m - m')))) := by
      rw [hexpfac]
      ring
    rw [hsplit] at hle
    exact le_of_mul_le_mul_left hle hk
  -- the bound tends to zero
  have hlim : Tendsto (fun τ : ℝ => C * Real.exp (-(τ * (m - m')))) atTop (𝓝 0) := by
    have harg : Tendsto (fun τ : ℝ => τ * (m - m')) atTop atTop :=
      (Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < m - m') tendsto_id).congr'
        (Eventually.of_forall fun τ => mul_comm _ _)
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).const_mul C
    simpa using h
  have hzero : (ρ (Set.Iio m')).toReal = 0 := by
    refine le_antisymm ?_ (by positivity)
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hmass τ hτ
  rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with h | h
  · exact hne h
  · exact (measure_ne_top ρ (Set.Iio m')) h

/-- **The Källén–Lehmann representation in a multiplication model.**  For a measure `μ`, a
measurable symbol `f` and a weight `w`, the pushed-forward weighted measure is the spectral measure
of multiplication by `f`, and its Laplace transform is the two-point function of the weight: the
measurable functional calculus `e^{−τM_f} = M_{e^{−τf}}`, integrated against `w`.  This is the
non-atomic form of `klCorr`: `ρ` is atomic only when `f` has atomic fibres. -/
theorem laplace_map_withDensity {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : Measurable f) {w : X → ENNReal} (hw : Measurable w)
    (hwtop : ∀ᵐ x ∂μ, w x < ∞) (τ : ℝ) :
    laplace ((μ.withDensity w).map f) τ
      = ∫ x, (w x).toReal * Real.exp (-(τ * f x)) ∂μ := by
  have hmeas : AEStronglyMeasurable (fun l : ℝ => Real.exp (-(τ * l)))
      ((μ.withDensity w).map f) :=
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable
  rw [laplace, integral_map hf.aemeasurable hmeas]
  rw [integral_withDensity_eq_integral_toReal_smul hw hwtop]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]

end KallenLehmannGeneral

end

end BookProof.OSReconstruction
