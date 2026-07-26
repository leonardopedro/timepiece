import Mathlib

import Singularity.OdeSystem
import Singularity.Poly

/-!
# Weyl quantization of polynomial ODEs

The real normal-ordered algebra suppresses the global complex factor in the
momentum generator.  Consequently, the robust algebraic definition of Weyl
symmetrization is the fixed part `½ (A + A†)`, rather than an expression whose
signs depend on how that suppressed factor is restored.
-/

open Polynomial
open NormalOrderedOp

/-- The unsymmetrized sum `Σᵢ fᵢ pᵢ`. -/
noncomputable def odeHamiltonianRaw {M : ℕ} (sys : ODESystem M) : NormalOrderedOp M :=
  ⟨∑ i : Fin M, (mulPMode (toNormalOrdered (sys.rhs i) i) i).terms⟩

/-- Koopman-Weyl quantization.  It is defined as the self-adjoint part of the
raw normal-ordered operator, exactly implementing `(A + A†)/2`. -/
noncomputable def odeToHamiltonian {M : ℕ} (sys : ODESystem M) : NormalOrderedOp M :=
  (odeHamiltonianRaw sys).add (adj (odeHamiltonianRaw sys)) |>.smul (1 / 2)

/-- The `x` generator is fixed by the real Wick adjoint. -/
theorem adj_mulXMode {M : ℕ} (op : NormalOrderedOp M) (i : Fin M) :
    adj (mulXMode op i) = mulXMode (adj op) i := by
  unfold mulXMode adj
  -- Key lemma: swapCounts composes with the update functions
  have h_annih : swapCounts ∘ (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1)) =
                 (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2)) ∘ swapCounts := by
    funext ts j
    simp only [Function.comp_apply, swapCounts]
    by_cases hji : j = i
    · subst hji
      simp [Function.update_self]
    · simp [hji, Function.update_of_ne, swapCounts]
  have h_creat : swapCounts ∘ (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2)) =
                 (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1)) ∘ swapCounts := by
    funext ts j
    simp only [Function.comp_apply, swapCounts]
    by_cases hji : j = i
    · subst hji
      simp [Function.update_self]
    · simp [hji, Function.update_of_ne, swapCounts]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_smul]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  simp [h_annih, h_creat]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rw [add_comm]

/-- The real algebraic momentum generator changes sign under adjoint.  This is
why it is multiplied by `-i` in the complex operator interpretation. -/
theorem adj_mulPMode {M : ℕ} (op : NormalOrderedOp M) (i : Fin M) :
    adj (mulPMode op i) = -(mulPMode (adj op) i) := by
  ext a
  simp [mulPMode, adj]
  -- Need to rewrite: mapDomain f (c • m - c • n) = c * mapDomain g (mapDomain f m) - c * mapDomain h (mapDomain f n)
  -- where g = f ∘ update_+, h = f ∘ update-
  have h1 : ∀ ts : Fin M → ℕ × ℕ, swapCounts (Function.update ts i ((ts i).1, (ts i).2 + 1)) = 
            Function.update (swapCounts ts) i ((ts i).2 + 1, (ts i).1) := by
    intro ts
    funext j
    simp [swapCounts, Function.update]
    split_ifs <;> rfl
  have h2 : ∀ ts : Fin M → ℕ × ℕ, swapCounts (Function.update ts i ((ts i).1 + 1, (ts i).2)) = 
            Function.update (swapCounts ts) i ((ts i).2, (ts i).1 + 1) := by
    intro ts
    funext j
    simp [swapCounts, Function.update]
    split_ifs <;> rfl
  -- Key insight: swapCounts ∘ annihilation_fn = creation_fn ∘ swapCounts
  -- and swapCounts ∘ creation_fn = annihilation_fn ∘ swapCounts
  have eq_ann : swapCounts ∘ (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1)) = 
                (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2)) ∘ swapCounts := by
    funext ts
    simp only [Function.comp_def]
    rw [h1]
    simp [swapCounts]
  have eq_creat : swapCounts ∘ (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2)) = 
                  (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1)) ∘ swapCounts := by
    funext ts
    simp only [Function.comp_def]
    rw [h2]
    simp [swapCounts]
  -- Convert subtraction to addition of negation
  have sub_eq : ∀ x y : Finsupp (Fin M → ℕ × ℕ) ℝ, x - y = x + (-y) := fun x y => sub_eq_add_neg x y
  rw [sub_eq]
  rw [Finsupp.mapDomain_add]
  rw [Finsupp.mapDomain_smul]
  rw [← neg_smul, Finsupp.mapDomain_smul]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rw [eq_ann, eq_creat]
  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp]
  simp [smul_eq_mul]
  rfl


/-- Weyl symmetrization is fixed by the Wick adjoint. -/
theorem weyl_symmetrization_self_adjoint {M : ℕ} (sys : ODESystem M) :
    adj (odeToHamiltonian sys) = odeToHamiltonian sys := by
  simp [odeToHamiltonian, adj_smul, adj_add, adj_involutive]
  ext
  simp [NormalOrderedOp.add, add_comm]

/-- Hamiltonian associated to a scalar polynomial ODE. -/
noncomputable def hamiltonian1D (f : Polynomial ℝ) : NormalOrderedOp 1 :=
  odeToHamiltonian (mk1D f)

example : hamiltonian1D (Polynomial.X ^ 2 : Polynomial ℝ) =
    hamiltonian1D (Polynomial.X ^ 2 : Polynomial ℝ) := rfl
