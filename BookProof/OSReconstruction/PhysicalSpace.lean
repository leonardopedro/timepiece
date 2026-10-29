import Mathlib
import BookProof.ReflectionPositivity.Proof

/-!
# The physical Hilbert space of OS reconstruction

Plan: `cftproof.md`, Phase 4.1 — "The OS form `⟨F, G⟩_phys = ω(θF ∘ G)`, with `ω` a state
satisfying RP, defines an inner product on `𝔄 / 𝔑` … its completion is the physical Hilbert
space `ℋ`".

## What is proved here

Let `ω` be a `θ`-invariant linear functional on the observables (`LinearFunctional`) which is
reflection positive (`IsReflectionPositive`).  Then:

* `osForm_add_left`, `osForm_smul_left`, `osForm_add_right'`, `osForm_smul_right'` — the OS form
  is `ℝ`-bilinear;
* `osForm_symm'` — it is symmetric, because `ω` is `θ`-invariant;
* `osForm_self_nonneg` — it is positive semidefinite, which **is** reflection positivity;
* `osForm_expand` — the quadratic expansion
  `⟨F + tG, F + tG⟩ = ⟨F,F⟩ + 2t⟨F,G⟩ + t²⟨G,G⟩`, the input to Cauchy–Schwarz;
* `osForm_cauchy_schwarz` — `⟨F,G⟩² ≤ ⟨F,F⟩⟨G,G⟩`;
* `Radical` — the radical `{F | ∀ G, ⟨F,G⟩ = 0}` (a submodule by construction), the `𝔑` of the
  plan's quotient, with `osForm_well_defined`: the form descends to it;
* `mem_radical_of_self_eq_zero` — the radical is exactly the null set (Cauchy–Schwarz);
* `osNorm`, `osNorm_nonneg`, `osNorm_triangle` — the OS seminorm and its triangle inequality.

## Boundary

The final assembly — putting the inner product on `𝔄 ⧸ 𝔑` and completing — is recorded, not
assembled here: the fields of `PreInnerProductSpace.Core` are exactly `osForm_symm'`,
`osForm_self_nonneg`, `osForm_add_left`, `osForm_smul_left` plus the descent
`osForm_well_defined`, and `InnerProductSpace.ofCore` with `UniformSpace.Completion`
(`Mathlib/Analysis/InnerProductSpace/Completion.lean`) supply the rest.  What is *not* proved is
the functoriality of the construction (Phase 4.1's last sentence): it needs maps of completions,
which the corpus does not have.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity

noncomputable section

/-- A `θ`-invariant linear functional on the observables: the expectation of a translation
invariant state.  (`map_theta` is what makes the OS form symmetric.) -/
structure LinearFunctional where
  toFun : Observable → ℝ
  map_add : ∀ F G : Observable, toFun (F + G) = toFun F + toFun G
  map_smul : ∀ (c : ℝ) (F : Observable), toFun (c • F) = c * toFun F
  map_theta : ∀ F : Observable, toFun (thetaObs F) = toFun F

instance : CoeFun LinearFunctional (fun _ => Observable → ℝ) := ⟨LinearFunctional.toFun⟩

/-- The OS form `⟨F, G⟩ = ω(θF · G)`. -/
def osBilin (ω : LinearFunctional) (F G : Observable) : ℝ := osForm ω F G

/-- `θ` is linear on observables. -/
theorem thetaObs_smul' (c : ℝ) (F : Observable) : thetaObs (c • F) = c • thetaObs F := by
  funext x
  simp only [thetaObs_apply, Pi.smul_apply]

/-- `θ` vanishes on `0`. -/
theorem thetaObs_zero : thetaObs (0 : Observable) = 0 := by
  funext x
  simp only [thetaObs_apply, Pi.zero_apply]

theorem osForm_zero (ω : LinearFunctional) : ω.toFun (0 : Observable) = 0 := by
  have h : ω.toFun (0 : Observable) = ω.toFun 0 + ω.toFun 0 := by
    simpa using ω.map_add (0 : Observable) 0
  linarith

/-! ## Bilinearity -/

theorem osForm_add_left (ω : LinearFunctional) (F G H : Observable) :
    osBilin ω (F + G) H = osBilin ω F H + osBilin ω G H := by
  simp only [osBilin, osForm, thetaObs_add, add_mul]
  exact ω.map_add _ _

theorem osForm_smul_left (ω : LinearFunctional) (c : ℝ) (F G : Observable) :
    osBilin ω (c • F) G = c * osBilin ω F G := by
  simp only [osBilin, osForm, thetaObs_smul', smul_mul_assoc]
  exact ω.map_smul c _

theorem osForm_add_right' (ω : LinearFunctional) (F G H : Observable) :
    osBilin ω F (G + H) = osBilin ω F G + osBilin ω F H :=
  osForm_add_right ω.toFun ω.map_add F G H

theorem osForm_smul_right' (ω : LinearFunctional) (c : ℝ) (F G : Observable) :
    osBilin ω F (c • G) = c * osBilin ω F G :=
  osForm_smul_right ω.toFun ω.map_smul F G c

/-- **Symmetry** of the OS form, from `θ`-invariance of `ω`. -/
theorem osForm_symm' (ω : LinearFunctional) (F G : Observable) :
    osBilin ω F G = osBilin ω G F :=
  osForm_symm (fun H => ω.map_theta H) F G

/-- **Positivity** of the form on the diagonal: reflection positivity, verbatim. -/
theorem osForm_self_nonneg (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (F : Observable) :
    0 ≤ osBilin ω F F :=
  hRP F

/-- The quadratic expansion of the form. -/
theorem osForm_expand (ω : LinearFunctional) (F G : Observable) (t : ℝ) :
    osBilin ω (F + t • G) (F + t • G) =
      osBilin ω F F + 2 * t * osBilin ω F G + t ^ 2 * osBilin ω G G := by
  have hFG : osBilin ω G F = osBilin ω F G := osForm_symm' ω G F
  rw [osForm_add_left, osForm_smul_left, osForm_add_right', osForm_smul_right',
    osForm_add_right', osForm_smul_right', hFG]
  ring

/-! ## The radical and the seminorm -/

/-- **The radical** `𝔑 = {F | ⟨F,G⟩ = 0 for all G}` — the null ideal of the OS form. -/
def Radical (ω : LinearFunctional) : Submodule ℝ Observable where
  carrier := {F | ∀ G : Observable, osBilin ω F G = 0}
  zero_mem' := by
    intro G
    simp only [osBilin, osForm, thetaObs_zero, zero_mul]
    exact osForm_zero ω
  add_mem' := by
    intro F H hF hH G
    rw [osForm_add_left, hF G, hH G, add_zero]
  smul_mem' := by
    intro c F hF G
    rw [osForm_smul_left, hF G, mul_zero]

theorem mem_radical_iff {ω : LinearFunctional} {F : Observable} :
    F ∈ Radical ω ↔ ∀ G : Observable, osBilin ω F G = 0 := Iff.rfl

/-- **Cauchy–Schwarz** for the OS form. -/
theorem osForm_cauchy_schwarz (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (F G : Observable) :
    osBilin ω F G ^ 2 ≤ osBilin ω F F * osBilin ω G G := by
  set a := osBilin ω F F with ha
  set b := osBilin ω F G with hb
  set c := osBilin ω G G with hc
  have ha0 : 0 ≤ a := osForm_self_nonneg ω hRP F
  have hc0 : 0 ≤ c := osForm_self_nonneg ω hRP G
  have key : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c := by
    intro t
    have h := osForm_self_nonneg ω hRP (F + t • G)
    rw [osForm_expand ω F G t, ← ha, ← hb, ← hc] at h
    exact h
  rcases lt_or_eq_of_le hc0 with hcpos | hc0'
  · have h := key (-b / c)
    have hquad : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp
      ring
    rw [hquad] at h
    have h' : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hcpos] at h'
    linarith
  · have hb0 : b = 0 := by
      by_contra hbne
      have h := key (-(a + 1) / (2 * b))
      rw [← hc0'] at h
      have hquad : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 =
          a - (a + 1) := by
        field_simp
        ring
      rw [hquad] at h
      linarith
    rw [hb0, ← hc0']
    simp

/-- Membership in the radical from vanishing on the diagonal (Cauchy–Schwarz). -/
theorem mem_radical_of_self_eq_zero (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) {F : Observable}
    (hF : osBilin ω F F = 0) : F ∈ Radical ω := by
  intro G
  have h := osForm_cauchy_schwarz ω hRP F G
  rw [hF, zero_mul] at h
  have hsq : osBilin ω F G ^ 2 = 0 := by linarith [sq_nonneg (osBilin ω F G)]
  exact pow_eq_zero_iff two_ne_zero |>.1 hsq

/-- **The form descends to the radical**: `⟨F, G⟩` depends only on the class of `F`. -/
theorem osForm_well_defined (ω : LinearFunctional) {F F' : Observable}
    (h : F - F' ∈ Radical ω) (G : Observable) : osBilin ω F G = osBilin ω F' G := by
  have h1 : osBilin ω (F - F') G = 0 := h G
  have hexp : osBilin ω (F - F') G = osBilin ω F G - osBilin ω F' G := by
    rw [sub_eq_add_neg, osForm_add_left]
    congr 1
    rw [show (-F' : Observable) = (-1 : ℝ) • F' from by simp]
    rw [osForm_smul_left]
    ring
  linarith

/-- The OS seminorm `‖F‖ = √⟨F,F⟩`. -/
def osNorm (ω : LinearFunctional) (F : Observable) : ℝ := Real.sqrt (osBilin ω F F)

theorem osNorm_nonneg (ω : LinearFunctional) (F : Observable) : 0 ≤ osNorm ω F :=
  Real.sqrt_nonneg _

theorem osNorm_sq (ω : LinearFunctional) (hRP : IsReflectionPositive (fun F => ω.toFun F))
    (F : Observable) : osNorm ω F ^ 2 = osBilin ω F F :=
  Real.sq_sqrt (osForm_self_nonneg ω hRP F)

/-- **The triangle inequality** for the OS seminorm, from Cauchy–Schwarz. -/
theorem osNorm_triangle (ω : LinearFunctional)
    (hRP : IsReflectionPositive (fun F => ω.toFun F)) (F G : Observable) :
    osNorm ω (F + G) ≤ osNorm ω F + osNorm ω G := by
  have hcs := osForm_cauchy_schwarz ω hRP F G
  have ha := osForm_self_nonneg ω hRP F
  have hc := osForm_self_nonneg ω hRP G
  have hb : osBilin ω F G ≤ Real.sqrt (osBilin ω F F) * Real.sqrt (osBilin ω G G) := by
    have h1 : osBilin ω F G ≤ |osBilin ω F G| := le_abs_self _
    have h2 : |osBilin ω F G| = Real.sqrt (osBilin ω F G ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    have h3 : Real.sqrt (osBilin ω F G ^ 2) ≤ Real.sqrt (osBilin ω F F * osBilin ω G G) :=
      Real.sqrt_le_sqrt hcs
    have h4 : Real.sqrt (osBilin ω F F * osBilin ω G G) =
        Real.sqrt (osBilin ω F F) * Real.sqrt (osBilin ω G G) :=
      Real.sqrt_mul ha _
    linarith
  have hFF : osBilin ω (F + G) (F + G) = osBilin ω F F + 2 * osBilin ω F G + osBilin ω G G := by
    have h := osForm_expand ω F G 1
    simpa using h
  have key : osBilin ω F F + 2 * osBilin ω F G + osBilin ω G G ≤
      (Real.sqrt (osBilin ω F F) + Real.sqrt (osBilin ω G G)) ^ 2 := by
    have h2 : osBilin ω F F = Real.sqrt (osBilin ω F F) ^ 2 := (Real.sq_sqrt ha).symm
    have h3 : osBilin ω G G = Real.sqrt (osBilin ω G G) ^ 2 := (Real.sq_sqrt hc).symm
    nlinarith [Real.sqrt_nonneg (osBilin ω F F), Real.sqrt_nonneg (osBilin ω G G)]
  have hmain : osNorm ω (F + G) ≤
      Real.sqrt ((Real.sqrt (osBilin ω F F) + Real.sqrt (osBilin ω G G)) ^ 2) := by
    rw [osNorm, hFF]
    exact Real.sqrt_le_sqrt key
  refine hmain.trans ?_
  rw [Real.sqrt_sq (by positivity)]
  rfl

end

end BookProof.OSReconstruction
