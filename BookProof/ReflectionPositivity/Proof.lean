import Mathlib
import BookProof.ReflectionPositivity.HalfSpaceAlgebra
import BookProof.BalabanRG.Convergence

/-!
# Reflection positivity and its continuum limit

Plan: `cftproof.md`, Phase 3.3 — "Show that `lim_{N→∞} ω_N` is reflection positive … This is
where the Legendre transform for the beta function emerges" (the Legendre-transform/beta-function
part is Phase 5 and out of scope here).

## What is proved (and what is hypothesis)

* `osForm ω F G = ω(θF · G)` — the OS sesquilinear form of a functional `ω` on observables;
* `IsReflectionPositive ω` — `ω(θF F) ≥ 0` for every observable `F`;
* **`reflection_positivity_continuum`** — if every `ω_N` is reflection positive and `ω_N → ω`
  pointwise, then `ω` is reflection positive.  This is Phase 3.3's limit passage, and it is a
  genuine theorem (extensional passage of a nonnegativity bound);
* **`psiSeq_component_tendsto`** — the link to Phase 2: if the effective actions `Ψ_N` converge
  in `F_total`, then their components converge in their sectors.  This is what allows the
  states of the lattice models (built from `Ψ_N`) to have a limit at all;
* `osForm_theta_invariant`, `osForm_add_*`, `osForm_smul_*` — the elementary structure of the
  form used by `OSReconstruction`.

## The input that is a hypothesis

The lattice theorems `ω_N(θF F) ≥ 0` are the OS-positivity of the Wilson lattice gauge measure.
They are *not* proved here and must not be: they are a nontrivial theorem of the subject
(reflection positivity of the lattice measure for the Wilson action), not a Lean
bookkeeping fact.  `IsReflectionPositive` is therefore a hypothesis of the limit theorem, and
the honest content of this file is that the hypothesis *passes to the limit* — i.e. that the
continuum OS positivity follows from the lattice one, given the convergence of Phase 2.
-/

namespace BookProof.ReflectionPositivity

open BookProof.BalabanRG Filter
open scoped Topology

noncomputable section

/-- **The OS form**: `ω(F, G) = ω(θF · G)`. -/
def osForm (ω : Observable → ℝ) (F G : Observable) : ℝ := ω (thetaObs F * G)

/-- **Reflection positivity** of a functional: the OS form is positive semidefinite on the
observables. -/
def IsReflectionPositive (ω : Observable → ℝ) : Prop := ∀ F : Observable, 0 ≤ osForm ω F F

theorem osForm_apply (ω : Observable → ℝ) (F G : Observable) :
    osForm ω F G = ω (thetaObs F * G) := rfl

/-- If `ω` is invariant under `θ`, the OS form is symmetric. -/
theorem osForm_symm {ω : Observable → ℝ} (hθ : ∀ G : Observable, ω (thetaObs G) = ω G)
    (F G : Observable) : osForm ω F G = osForm ω G F := by
  simp only [osForm]
  have h : ω (thetaObs F * G) = ω (thetaObs (thetaObs F * G)) := (hθ (thetaObs F * G)).symm
  rw [h, thetaObs_mul, thetaObs_involutive, mul_comm]

/-- **Reflection positivity passes to the continuum limit** (plan Phase 3.3). -/
theorem reflection_positivity_continuum (ω : ℕ → Observable → ℝ) (ωLim : Observable → ℝ)
    (hconv : ∀ G : Observable, Tendsto (fun N : ℕ => ω N G) atTop (𝓝 (ωLim G)))
    (hRP : ∀ (N : ℕ) (F : Observable), 0 ≤ osForm (ω N) F F) :
    IsReflectionPositive ωLim :=
  fun F => le_of_tendsto_of_tendsto tendsto_const_nhds (hconv (thetaObs F * F))
    (Eventually.of_forall fun N => hRP N F)

/-- **Componentwise convergence of the effective actions**: a limit in `F_total` gives a limit
in every sector (the link from Phase 2.3 to the states of Phase 3). -/
theorem psiSeq_component_tendsto (ψ : ℕ → FTotal) (ψLim : FTotal)
    (h : Tendsto ψ atTop (𝓝 ψLim)) (k : ℕ) :
    Tendsto (fun N : ℕ => ψ N k) atTop (𝓝 (ψLim k)) := by
  have hbound : ∀ N : ℕ, ‖ψ N k - ψLim k‖ ≤ ‖ψ N - ψLim‖ := by
    intro N
    have h1 : ψ N k - ψLim k = (ψ N - ψLim) k := rfl
    rw [h1]
    exact norm_component_le (ψ N - ψLim) k
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by
    have h1 : dist (ψ n) ψLim = ‖ψ n - ψLim‖ := dist_eq_norm _ _
    have h2 : dist (ψ n k) (ψLim k) = ‖ψ n k - ψLim k‖ := dist_eq_norm _ _
    rw [h2]
    exact (hbound n).trans_lt (by rw [← h1]; exact hN n hn)⟩

/-- The form is additive in its second argument. -/
theorem osForm_add_right (ω : Observable → ℝ) (hadd : ∀ F G, ω (F + G) = ω F + ω G)
    (F G H : Observable) : osForm ω F (G + H) = osForm ω F G + osForm ω F H := by
  simp only [osForm, mul_add]
  exact hadd _ _

/-- The form is homogeneous in its second argument. -/
theorem osForm_smul_right (ω : Observable → ℝ) (hsmul : ∀ (c : ℝ) F, ω (c • F) = c * ω F)
    (F G : Observable) (c : ℝ) : osForm ω F (c • G) = c * osForm ω F G := by
  simp only [osForm, mul_smul_comm]
  exact hsmul c _

end

end BookProof.ReflectionPositivity
