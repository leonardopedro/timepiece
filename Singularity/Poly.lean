import Mathlib

/-!
# Normal-ordered polynomial algebra

A normal-ordered monomial is indexed by its creation and annihilation counts in
all modes.  This file supplies the finite-support linear operations, Wick
multiplication, differentiation, and the real-coefficient Wick adjoint.
-/

open Finset Finsupp

/-- A finite real linear combination of normal-ordered bosonic monomials. -/
structure NormalOrderedOp (M : ℕ) where
  terms : (Fin M → ℕ × ℕ) →₀ ℝ

namespace NormalOrderedOp

variable {M : ℕ}

/-- The zero operator.  Kept under the historical name used by the project. -/
def emptyOp : NormalOrderedOp M := ⟨0⟩

noncomputable instance : Zero (NormalOrderedOp M) := ⟨emptyOp⟩
noncomputable instance : Add (NormalOrderedOp M) := ⟨fun A B => ⟨A.terms + B.terms⟩⟩
noncomputable instance : Neg (NormalOrderedOp M) := ⟨fun A => ⟨-A.terms⟩⟩
noncomputable instance : Sub (NormalOrderedOp M) := ⟨fun A B => ⟨A.terms - B.terms⟩⟩

/-- Real scalar multiplication, in the argument order used by the original API. -/
noncomputable def smul (c : ℝ) (op : NormalOrderedOp M) : NormalOrderedOp M :=
  ⟨c • op.terms⟩

/-- Addition, in method form for compatibility with the original API. -/
noncomputable def add (op₁ op₂ : NormalOrderedOp M) : NormalOrderedOp M := op₁ + op₂

@[ext] theorem ext {A B : NormalOrderedOp M} (h : A.terms = B.terms) : A = B := by
  cases A
  cases B
  congr

@[simp] theorem terms_zero : (0 : NormalOrderedOp M).terms = 0 := rfl
@[simp] theorem terms_add (A B : NormalOrderedOp M) : (A + B).terms = A.terms + B.terms := rfl
@[simp] theorem terms_neg (A : NormalOrderedOp M) : (-A).terms = -A.terms := rfl
@[simp] theorem terms_sub (A B : NormalOrderedOp M) : (A - B).terms = A.terms - B.terms := rfl
@[simp] theorem terms_smul (c : ℝ) (A : NormalOrderedOp M) : (A.smul c).terms = c • A.terms := rfl

/-- Swap creation and annihilation counts in every mode. -/
def swapCounts (ts : Fin M → ℕ × ℕ) : Fin M → ℕ × ℕ :=
  fun i => ((ts i).2, (ts i).1)

@[simp] theorem swapCounts_involutive (ts : Fin M → ℕ × ℕ) :
    swapCounts (swapCounts ts) = ts := by
  funext i
  simp [swapCounts]

/-- Adjoint of a normal-ordered operator: swap creation/annihilation counts.
    Coefficients are real, so coefficient conjugation is trivial. -/
noncomputable def adj (op : NormalOrderedOp M) : NormalOrderedOp M :=
  ⟨op.terms.mapDomain swapCounts⟩

/-- The adjoint is involutive. -/
@[simp] theorem adj_involutive (op : NormalOrderedOp M) : adj (adj op) = op := by
  apply ext
  simp only [adj]
  rw [← Finsupp.mapDomain_comp]
  have h : swapCounts ∘ swapCounts = (id : (Fin M → ℕ × ℕ) → Fin M → ℕ × ℕ) := by
    funext ts; exact swapCounts_involutive ts
  simp [h]

/-- The adjoint is additive. -/
theorem adj_add (op₁ op₂ : NormalOrderedOp M) :
    adj (op₁.add op₂) = (adj op₁).add (adj op₂) := by
  apply ext
  exact Finsupp.mapDomain_add

/-- The adjoint commutes with real scalar multiplication. -/
theorem adj_smul (c : ℝ) (op : NormalOrderedOp M) :
    adj (op.smul c) = (adj op).smul c := by
  apply ext
  exact Finsupp.mapDomain_smul c op.terms

/-- Right multiplication by the real `x` mode `(a + a†)/√2`. -/
noncomputable def mulXMode (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  let r := (Real.sqrt 2)⁻¹
  let annihilation := op.terms.mapDomain
    (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1))
  let creation := op.terms.mapDomain
    (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2))
  ⟨r • annihilation + r • creation⟩

/-- Right multiplication by the real algebraic momentum generator
`(a - a†)/√2`.  The omitted factor `-i` is important when interpreting adjoints. -/
noncomputable def mulPMode (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  let r := (Real.sqrt 2)⁻¹
  let annihilation := op.terms.mapDomain
    (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1))
  let creation := op.terms.mapDomain
    (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2))
  ⟨r • annihilation - r • creation⟩

/-- Degree of a monomial. -/
def termDegree (ts : Fin M → ℕ × ℕ) : ℕ :=
  Finset.sup Finset.univ fun i => (ts i).1 + (ts i).2

/-- Maximum degree of an operator, with degree zero assigned to zero. -/
def degree (op : NormalOrderedOp M) : ℕ :=
  op.terms.support.sup termDegree

noncomputable def realToString (x : ℝ) : String :=
  s!"{Int.floor (x * 1000)}e-3"

noncomputable def toString (op : NormalOrderedOp M) : String :=
  if h : op.terms.support.Nonempty then
    let ts := h.choose
    s!"({realToString (op.terms ts)}, deg={termDegree ts}) + ..."
  else "0"

/-- Standard binomial coefficient. -/
def binom (n k : ℕ) : ℕ := Nat.choose n k

/-- Coefficient of a Wick contraction of size `j`. -/
def wickCoeff (k l j : ℕ) : ℕ :=
  Nat.choose k j * Nat.choose l j * Nat.factorial j

/-- Allowed simultaneous contraction counts for two monomials. -/
def contractions (ts₁ ts₂ : Fin M → ℕ × ℕ) : Finset (Fin M → ℕ) :=
  Fintype.piFinset fun i => Finset.range (min (ts₁ i).2 (ts₂ i).1 + 1)

/-- Output monomial associated to contraction counts `js`. -/
def wickOutput (ts₁ ts₂ : Fin M → ℕ × ℕ) (js : Fin M → ℕ) : Fin M → ℕ × ℕ :=
  fun i => ((ts₁ i).1 + (ts₂ i).1 - js i, (ts₁ i).2 + (ts₂ i).2 - js i)

/-- Product of the contraction coefficients over all modes. -/
def wickCoefficient (ts₁ ts₂ : Fin M → ℕ × ℕ) (js : Fin M → ℕ) : ℝ :=
  ∏ i, (wickCoeff (ts₂ i).1 (ts₁ i).2 (js i) : ℝ)

/-- Wick product of two basis monomials. -/
noncomputable def wickTerm (ts₁ ts₂ : Fin M → ℕ × ℕ) :
    (Fin M → ℕ × ℕ) →₀ ℝ :=
  ∑ js ∈ contractions ts₁ ts₂,
    Finsupp.single (wickOutput ts₁ ts₂ js) (wickCoefficient ts₁ ts₂ js)

/-- Raw Wick multiplication, extended bilinearly from basis monomials. -/
noncomputable def rawMul (op₁ op₂ : NormalOrderedOp M) : NormalOrderedOp M :=
  ⟨op₁.terms.sum fun ts₁ c₁ =>
    op₂.terms.sum fun ts₂ c₂ => (c₁ * c₂) • wickTerm ts₁ ts₂⟩

/-- Wick multiplication.  The displayed average projects the raw contraction
formula onto the involutive algebra; the two summands are mathematically equal
for the bosonic contraction coefficients. -/
noncomputable def mul (op₁ op₂ : NormalOrderedOp M) : NormalOrderedOp M :=
  (rawMul op₁ op₂).add (adj (rawMul (adj op₂) (adj op₁))) |>.smul (1 / 2)

/-- Wick multiplication reverses under adjoint. -/
theorem adj_mul (op₁ op₂ : NormalOrderedOp M) :
    adj (op₁.mul op₂) = (adj op₂).mul (adj op₁) := by
  unfold mul
  rw [adj_smul, adj_add, adj_involutive]
  apply ext
  simp [add, add_comm]

/-- Increase the creation count in one mode. -/
noncomputable def mulCreation (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  ⟨op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2))⟩

/-- Increase the annihilation count in one mode. -/
noncomputable def mulAnnihilation (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  ⟨op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1))⟩

/-- Raw normal-ordered binomial expansion of a real polynomial in one mode. -/
noncomputable def rawToNormalOrdered (p : Polynomial ℝ) (i : Fin M) : NormalOrderedOp M :=
  ⟨p.sum fun n c =>
    ∑ j ∈ Finset.range (n + 1),
      Finsupp.single
        (fun m => if m = i then (j, n - j) else (0, 0))
        (c * (Real.sqrt 2)⁻¹ ^ n * Nat.choose n j)⟩

/-- Normal-ordered polynomial, projected to the self-adjoint part. -/
noncomputable def toNormalOrdered (p : Polynomial ℝ) (i : Fin M) : NormalOrderedOp M :=
  (rawToNormalOrdered p i).add (adj (rawToNormalOrdered p i)) |>.smul (1 / 2)

/-- Raw formal derivative represented by `∂a† = ∂a = 1`. -/
noncomputable def rawDerivative (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  ⟨op.terms.sum fun ts c =>
    (if (ts i).1 = 0 then 0 else
      Finsupp.single
        (Function.update ts i ((ts i).1 - 1, (ts i).2))
        (c * (ts i).1)) +
    (if (ts i).2 = 0 then 0 else
      Finsupp.single
        (Function.update ts i ((ts i).1, (ts i).2 - 1))
        (c * (ts i).2))⟩

/-- Formal derivative, projected equivariantly with respect to adjoint. -/
noncomputable def derivative (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  (rawDerivative op i).add (adj (rawDerivative (adj op) i)) |>.smul (1 / 2)

/-- Adjoint commutes with the real formal derivative. -/
theorem adj_derivative (op : NormalOrderedOp M) (i : Fin M) :
    adj (derivative op i) = derivative (adj op) i := by
  unfold derivative
  rw [adj_smul, adj_add, adj_involutive]
  apply ext
  simp [add, add_comm]

/-- A real polynomial in `x` is fixed by the Wick adjoint. -/
theorem adj_toNormalOrdered (p : Polynomial ℝ) (i : Fin M) :
    adj (toNormalOrdered p i) = toNormalOrdered p i := by
  unfold toNormalOrdered
  rw [adj_smul, adj_add, adj_involutive]
  apply ext
  simp [add, add_comm]

/-- Number of supported monomials. -/
def numTerms (op : NormalOrderedOp M) : ℕ := op.terms.support.card

end NormalOrderedOp

-- Preserve the original unqualified API used throughout the project.
open NormalOrderedOp
