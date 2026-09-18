import Mathlib
import BookProof.ChapterQgBrstDerivativeGauge
import BookProof.ChapterQgVielbeinScalaronGaugeFL

/-!
# Fourier elimination of the derivative variables — the quantum-gravity vielbein sector

Item 7 of the quantum-gravity plan items of `CONSOLIDATED_PLAN.md`: the derivative modes of the
vielbein sector are **eliminated**, not gauge-fixed.  The gauge condition of
`BookProof/ChapterQgBrstDerivativeGauge.lean` reads `D_{μν}^i(k) = i k_μ e_ν^i(k)`; read as a
*substitution to be used when defining the operator*, it says that the auxiliary derivative
variables never have to exist: every torsion form is, from the start, a linear form in the
**physical** vielbein modes `CMode` alone.  (As everywhere in this thread the overall factor `i` of
the derivative symbol is a phase and is omitted; it cancels in the Gram matrix.)

What is proved here:

* `elimD` — the elimination `σ(D_{μν}^i(k)) = k_μ e_ν^i(k)` as a linear form on `CMode`, and
  `elimTorsion k mu nu i = elimD k mu nu i − elimD k nu mu i` — the torsion `T = D − Dᵀ` *after*
  the substitution.  Both have type `CMode → ℂ`: **the extended mode space `EMode` never appears**,
  neither in the definition nor in the domain of the operator built from it.
* `elimTorsion_eq_torsionCoef` — the eliminated torsion is exactly the physical Fourier torsion
  `k_μ e_ν^i − k_ν e_μ^i` at momentum `k` (and zero on the other momenta), so the substitution is
  lossless; `elimTorsion_eq_gaugeReduce` identifies it with the gauge-reduced extended form of the
  BRST chapter, which is how that chapter's two identities are *restated* as an elimination.
* `elimTorsion_antisymm`, `elimTorsion_diag`, `elimTorsion_conj` — the structural facts (the
  torsion is antisymmetric in the derivative indices, vanishes on the diagonal and is
  real-coefficient).
* `elimGram_eq_contTorsionGram` — the Gram matrix of *all* eliminated torsion forms is exactly the
  vielbein self-interaction `contTorsionGram` of the continuum model, with **no** hypothesis
  relating the two momenta (off the momentum diagonal both sides vanish).
* `qgElimModes` and `qgElim_esa` / `starobinsky_qgElim_esa` — consequently the mode data of the
  eliminated presentation is the continuum mode data (`qgElimModes_A` states that its
  self-interaction matrix *is* the eliminated Gram matrix), and the quantum-gravity Hamiltonian it
  defines is essentially self-adjoint on the outer Fock space, with the full exponential
  Einstein-frame scalaron wall and arbitrary coupling constant.  No BRST charge, no ghost sector
  and no restriction-to-a-subset argument is used: the physical torsion is the only torsion from
  the start.
* `elimConfig` and `formValue_dGauge_elimConfig` / `eq_elimConfig_of_gauge_fixed` — in the *full*
  vielbein–scalaron model of `ChapterQgVielbeinScalaronGaugeFL`, whose modes carry the nine
  vielbein components together with the twenty-seven derivative components, the elimination
  parameterizes the derivative-gauge constraint surface **exactly**: an eliminated configuration
  satisfies all twenty-seven constraints identically, and every configuration satisfying them is
  eliminated.  On that surface the torsion form is the exact Fourier torsion
  (`formValue_torsion_elimConfig`) and the 3D transverse form is unchanged
  (`formValue_gauge3d_elimConfig`).
* `elimTorsion_ne_zero` — the eliminated torsion is not the zero form, so the statement is not
  vacuous.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgFourierElim

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.QgBrstDerivativeGauge
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL
open BookProof.QgVielbeinScalaronGaugeFL

noncomputable section

/-! ## 1. The elimination of the derivative modes -/

/-- **The elimination** `σ(D_{μν}^i(k)) = k_μ e_ν^i(k)`: the auxiliary derivative variable is
replaced, *in the definition of the operator*, by the momentum weight times the vielbein mode.  The
result is a linear form on the physical modes `CMode` — the auxiliary mode space does not occur. -/
def elimD (k : Mom) (mu nu i : Fin 3) (z : CMode) : ℂ :=
  if z.1 = k then (if z.2 = (nu, i) then ((k mu : ℤ) : ℂ) else 0) else 0

/-- **The eliminated torsion** `T_{μν}^i = σ(D_{μν}^i) − σ(D_{νμ}^i)`. -/
def elimTorsion (k : Mom) (mu nu i : Fin 3) (z : CMode) : ℂ :=
  elimD k mu nu i z - elimD k nu mu i z

/-- **The eliminated torsion is the physical Fourier torsion** `k_μ e_ν^i − k_ν e_μ^i` at the
momentum `k`, and zero on every other momentum: the substitution loses nothing. -/
theorem elimTorsion_eq_torsionCoef (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    elimTorsion k mu nu i z = if z.1 = k then torsionCoef k mu nu i z else 0 := by
  by_cases hk : z.1 = k
  · simp only [elimTorsion, elimD, torsionCoef, if_pos hk]
  · simp only [elimTorsion, elimD, if_neg hk, sub_zero]

/-- **The elimination restates the BRST gauge reduction.**  The eliminated torsion form is exactly
the form the gauge condition produces from the extended torsion `D_{μν}^i − D_{νμ}^i`; the
difference is that the left-hand side never mentions the extended mode space. -/
theorem elimTorsion_eq_gaugeReduce (k : Mom) (mu nu i : Fin 3) (x : CMode) :
    elimTorsion k mu nu i x = gaugeReduce (extTorsionCoef k mu nu i) x := by
  rw [elimTorsion_eq_torsionCoef, gaugeReduce_extTorsionCoef]

/-- The torsion is antisymmetric in the two derivative indices. -/
theorem elimTorsion_antisymm (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    elimTorsion k nu mu i z = -elimTorsion k mu nu i z := by
  simp only [elimTorsion]
  ring

/-- Hence it vanishes when the two derivative indices agree. -/
theorem elimTorsion_diag (k : Mom) (mu i : Fin 3) (z : CMode) :
    elimTorsion k mu mu i z = 0 := by
  simp only [elimTorsion, sub_self]

/-- The eliminated torsion form has real coefficients. -/
theorem elimTorsion_conj (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    (starRingEnd ℂ) (elimTorsion k mu nu i z) = elimTorsion k mu nu i z := by
  rw [elimTorsion_eq_torsionCoef]
  split
  · exact torsionCoef_conj k mu nu i z
  · exact map_zero _

/-! ## 2. The vielbein self-interaction of the eliminated presentation -/

/-- **The Gram matrix of all eliminated torsion forms** — the vielbein self-interaction
`½ Σ_m T_m²` of the eliminated presentation. -/
def elimGram (x y : CMode) : ℂ :=
  ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
    (starRingEnd ℂ) (elimTorsion x.1 mu nu i x) * elimTorsion x.1 mu nu i y

/-- **The eliminated self-interaction is the continuum one**, with no hypothesis on the momenta:
on the momentum diagonal both sides are the torsion Gram matrix, and off it both vanish (momentum
conservation), because the eliminated torsion at momentum `x.1` is supported on that momentum. -/
theorem elimGram_eq_contTorsionGram (x y : CMode) : elimGram x y = contTorsionGram x y := by
  by_cases h : x.1 = y.1
  · have hy : y.1 = x.1 := h.symm
    simp only [elimGram, contTorsionGram, if_pos h]
    refine Finset.sum_congr rfl fun mu _ => Finset.sum_congr rfl fun nu _ =>
      Finset.sum_congr rfl fun i _ => ?_
    rw [elimTorsion_eq_torsionCoef, elimTorsion_eq_torsionCoef, if_pos rfl, if_pos hy]
  · have hy : ¬ y.1 = x.1 := fun hh => h hh.symm
    simp only [elimGram, contTorsionGram, if_neg h]
    refine Finset.sum_eq_zero fun mu _ => Finset.sum_eq_zero fun nu _ =>
      Finset.sum_eq_zero fun i _ => ?_
    have hzero : elimTorsion x.1 mu nu i y = 0 := by
      rw [elimTorsion_eq_torsionCoef, if_neg hy]
    rw [hzero, mul_zero]

theorem elimGram_funext : elimGram = contTorsionGram := by
  funext x y
  exact elimGram_eq_contTorsionGram x y

/-! ## 3. The Hamiltonian of the eliminated presentation, and its essential self-adjointness -/

/-- **The mode data of the eliminated presentation.**  Its vielbein self-interaction is the Gram
matrix of the eliminated torsion forms (`qgElimModes_A`), and since that matrix *is*
`contTorsionGram`, the data is the continuum mode data — built on the physical modes only. -/
def qgElimModes (g : ℝ) : QgModeData CMode := qgContinuumModes g

/-- The self-interaction matrix of the eliminated presentation is the eliminated Gram matrix. -/
theorem qgElimModes_A (g : ℝ) : (qgElimModes g).A = elimGram := elimGram_funext.symm

/-- **The quantum-gravity Hamiltonian of the eliminated presentation is essentially self-adjoint**
on the outer Fock space, for an arbitrary smooth non-negative scalaron wall and an arbitrary
coupling constant: the derivative variables were eliminated when the operator was defined, so no
BRST charge, no ghost sector and no restriction argument enters. -/
theorem qgElim_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (qgElimModes g)).dom (secData W (qgElimModes g)).ext :=
  qgContinuum_essentiallySelfAdjointOn W g

/-- The same with the full exponential Einstein-frame Starobinsky wall. -/
theorem starobinsky_qgElim_esa (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    EssentiallySelfAdjointOn
        (secN (starobinskyWall M alpha halpha) (qgElimModes g)).dom
      (secData (starobinskyWall M alpha halpha) (qgElimModes g)).ext :=
  starobinsky_qgContinuum_esa M alpha halpha g

/-! ## 4. The full vielbein–scalaron model: the elimination *is* the gauge surface

In the full model of `ChapterQgVielbeinScalaronGaugeFL` a mode carries `36` components per
momentum — the nine vielbein components `e_ν^i` **and** the twenty-seven derivative components
`D_{μν}^i` — and the derivative-gauge forms `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i` cut out the
surface on which the latter are the derivatives of the former.  The elimination `elimConfig`
parameterizes exactly that surface by the nine vielbein components: every eliminated
configuration satisfies all twenty-seven constraints identically (`formValue_dGauge_elimConfig`),
and conversely every configuration satisfying them is an eliminated one
(`eq_elimConfig_of_gauge_fixed`).  On it the torsion form is the exact Fourier torsion
(`formValue_torsion_elimConfig`) and the 3D transverse gauge form is unchanged
(`formValue_gauge3d_elimConfig`).

Honest boundary: the Hamiltonian of that chapter is still *defined* on all `36` components, and
its essential self-adjointness (`qgFull_esa_farisLavine`) is the statement proved there; what is
added here is that the derivative components carry no independent content — the constraint surface
is the image of the elimination — so the eliminated presentation describes the same physics with
the nine vielbein components alone. -/

/-- **The elimination on configurations of the full model**: the nine vielbein components are kept
and each derivative component is *defined* to be `i k_μ e_ν^i`. -/
def elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) : Comp → ℂ
  | Sum.inl (nu, i) => z (nu, i)
  | Sum.inr (mu, nu, i) => Complex.I * ((k mu : ℤ) : ℂ) * z (nu, i)

@[simp] theorem elimConfig_e (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (nu i : Fin 3) :
    elimConfig k z (eIdx nu i) = z (nu, i) := rfl

@[simp] theorem elimConfig_d (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    elimConfig k z (dIdx mu nu i) = Complex.I * ((k mu : ℤ) : ℂ) * z (nu, i) := rfl

/-- **The derivative-gauge constraints are solved identically by the elimination**: no constraint
has to be imposed, and no ghost sector is needed, because the eliminated configuration satisfies
`D_{μν}^i − i k_μ e_ν^i = 0` by construction. -/
theorem formValue_dGauge_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    formValue k (dGaugeF mu nu i) (elimConfig k z) = 0 := by
  rw [formValue_dGauge, elimConfig_d, elimConfig_e, sub_self]

/-- **Conversely, every gauge-fixed configuration is an eliminated one**: the elimination
parameterizes the constraint surface exactly, by the nine vielbein components. -/
theorem eq_elimConfig_of_gauge_fixed (k : Mom) (w : Comp → ℂ)
    (h : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) :
    w = elimConfig k (fun p => w (eIdx p.1 p.2)) := by
  funext c
  match c with
  | Sum.inl (nu, i) => rfl
  | Sum.inr (mu, nu, i) =>
      have h1 := h mu nu i
      rw [formValue_dGauge] at h1
      change w (dIdx mu nu i) = Complex.I * ((k mu : ℤ) : ℂ) * w (eIdx nu i)
      linear_combination h1

/-- **On the eliminated configurations the torsion is the exact Fourier torsion**
`i(k_μ e_ν^i − k_ν e_μ^i)`. -/
theorem formValue_torsion_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    formValue k (torsionF mu nu i) (elimConfig k z)
      = Complex.I * (((k mu : ℤ) : ℂ) * z (nu, i) - ((k nu : ℤ) : ℂ) * z (mu, i)) := by
  rw [formValue_torsion, elimConfig_d, elimConfig_d]
  ring

/-- The 3D transverse gauge form is untouched by the elimination: it involves the vielbein
components only. -/
theorem formValue_gauge3d_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    formValue k (gauge3dF i) (elimConfig k z)
      = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * z (mu, i) := by
  rw [formValue_gauge3d]
  exact Finset.sum_congr rfl fun mu _ => by rw [elimConfig_e]

/-! ## 5. Non-vacuity -/

/-- The eliminated torsion is not the zero form: at the momentum `k = (1,1,1)` the component
`T_{01}^0` takes the value `1` on the mode `e_1^0(k)`. -/
theorem elimTorsion_ne_zero :
    elimTorsion (fun _ => (1 : ℤ)) 0 1 0 ((fun _ => (1 : ℤ)), 1, 0) ≠ 0 := by
  simp only [elimTorsion, elimD]
  norm_num [Prod.ext_iff]

end

end BookProof.QgFourierElim
