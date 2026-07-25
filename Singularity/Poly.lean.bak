import Mathlib

/-!
# S1: Normal-Ordered Polynomial Algebra

Implements Wick's recursive relations natively for normal-ordered
polynomials in the bosonic Fock algebra.  A normal-ordered operator
is a finite sum of terms `cᵢ · (a†^kᵢ a^lᵢ)` per mode, with real
coefficients.  Multiplication by `xᵢ` and `pᵢ` (the bosonic
mapping) is implemented via `(a + a†)/√2` and `-i(a - a†)/√2`.

## Key definitions

- `NormalOrderedOp M` — a normal-ordered operator on M modes
- `mulXMode op i` — right-multiply by the xᵢ bosonic mode
- `mulPMode op i` — right-multiply by the pᵢ bosonic mode
- `mul op1 op2` — Wick multiplication of two normal-ordered operators
- `toNormalOrdered p` — convert a polynomial to normal-ordered form
- `derivative op i` — differentiate a normal-ordered operator w.r.t. mode i
- `degree op` — maximum a†^k a^l count across all terms
- `toString` — pretty-printing for debugging
-/

open Complex
open Finset
open Finsupp

/-- A normal-ordered operator on M bosonic modes.
    Terms are keyed by a vector of `(creations, annihilations)` pairs,
    one entry per mode.  The coefficient is real.
    Only finitely many (k,l) vectors have nonzero coefficient.
    Uses `Finsupp` for finite support. -/
structure NormalOrderedOp (M : ℕ) where
  terms : (Fin M → ℕ × ℕ) →₀ ℝ

/-- Empty operator (identity). -/
def emptyOp : NormalOrderedOp M :=
  { terms := 0 }

/-- Scalar multiplication: multiply all coefficients by c. -/
noncomputable def smul (c : ℝ) (op : NormalOrderedOp M) : NormalOrderedOp M :=
  { terms := c • op.terms }

/-- Addition of two normal-ordered operators. -/
noncomputable def add (op1 op2 : NormalOrderedOp M) : NormalOrderedOp M :=
  { terms := op1.terms + op2.terms }

/-- Multiplication by the x-mode (creation + annihilation):
    `(aᵢ + aᵢ†)/√2`.  Uses the bosonic commutation relation
    `[aᵢ, aⱼ†] = δᵢⱼ` to reorder terms into normal form.

    For a normal-ordered term c · a†^k a^l, right-multiplying by xᵢ gives:
    c/√2 · a†^(k+1) a^l + c·l/√2 · a†^k a^(l-1)  (if l > 0)
    The second term vanishes when l = 0. -/
noncomputable def mulXMode (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  let sqrt2_inv := (Real.sqrt 2)⁻¹
  let aTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
    op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1))
  let aDaggerTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
    op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2))
  { terms :=
    (sqrt2_inv • aTerm) + (sqrt2_inv • aDaggerTerm) }

/-- Multiply a normal-ordered operator by the p-mode: `-i(aᵢ - aᵢ†)/√2`.
    Uses the bosonic commutation relation `[aᵢ, aⱼ†] = δᵢⱼ`.

    pᵢ = (-i/√2) · aᵢ + (i/√2) · aᵢ†

    Right-multiplying by pᵢ gives two terms:
    1. (-1/√2) · right-multiply by aᵢ → (kᵢ, lᵢ+1) with coefficient -c/√2
    2. (1/√2) · right-multiply by aᵢ† → (kᵢ+1, lᵢ) with coefficient c/√2

    Note: The i factor is implicit in the Hamiltonian layer; here we track
    the real algebraic structure only. -/
noncomputable def mulPMode (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  let sqrt2_inv := (Real.sqrt 2)⁻¹
  let aTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
    op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1))
  let aDaggerTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
    op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2))
  { terms := (sqrt2_inv • aTerm) - (sqrt2_inv • aDaggerTerm) }

/-- Degree of a single term: max_{j} (k_j + l_j) where (k_j, l_j) = ts j. -/
def termDegree (ts : Fin M → ℕ × ℕ) : ℕ :=
  Finset.sup (Finset.univ : Finset (Fin M)) fun j =>
    let (k, l) := ts j
    k + l

/-- Degree of a normal-ordered operator: maximum a†^k a^l count across all terms.
    For each mode i, the degree is k + l (creations + annihilations),
    and the overall degree is the maximum over all terms and modes. -/
def degree (op : NormalOrderedOp M) : ℕ :=
  if h : op.terms.support.Nonempty then
    Finset.sup' (Finset.image termDegree op.terms.support) (Finset.image_nonempty.mpr h) id
  else 0

/-- Helper to convert ℝ to String for debugging. -/
noncomputable def realToString (x : ℝ) : String :=
  -- Use a simple decimal approximation for debugging
  let n := Int.floor (x * 1000)
  s!"{n.toNat / 1000}"

/-- Pretty-print a normal-ordered operator for debugging. -/
noncomputable def toString (op : NormalOrderedOp M) : String :=
  let terms := op.terms.support
  if h : terms.Nonempty then
    let ts := h.choose
    let c := op.terms ts
    let d := termDegree ts
    s!"({realToString c}, deg={d}) + ..."
  else
    "0"

/-!
## Wick Multiplication

### Commutation lemma: a^l · a†^k = Σⱼ (k choose j)(l choose j)j! · a†^(k-j) a^(l-j)

This is the core Wick relation for bosonic operators with [a, a†] = 1.
-/

/-- The binomial coefficient `choose n k` as a natural number (zero if k > n). -/
def binom (n k : ℕ) : ℕ :=
  if h : k ≤ n then
    (Finset.range (k+1)).prod fun j => (n - j) / (k - j)
  else 0

/-- Wick contraction coefficient: `a^l · a†^k → Σⱼ C(k,l,j) · a†^(k-j) a^(l-j)`
    where `C(k,l,j) = (k choose j) * (l choose j) * j!` -/
def wickCoeff (k l j : ℕ) : ℕ :=
  (binom k j) * (binom l j) * (Nat.factorial j)

/-- Single-term Wick contraction: given (k₁,l₁) and (k₂,l₂), compute
    all output terms (k₁+k₂-j, l₁+l₂-j) with coefficients.
    Returns a Finsupp mapping output pairs to coefficients. -/
def wickTerm (ts1 ts2 : Fin M → ℕ × ℕ) : (Fin M → ℕ × ℕ) →₀ ℝ :=
  let F := Finset.univ (α := Fin M)
  F.fold (fun (acc : (Fin M → ℕ × ℕ) →₀ ℝ) (j : Fin M) =>
    let (k₁, l₁) := ts1 j
    let (k₂, l₂) := ts2 j
    let maxJ := min l₁ k₂
    -- For each j from 0 to maxJ, add the contracted term
    (Finset.range (maxJ+1)).fold (fun (acc' : (Fin M → ℕ × ℕ) →₀ ℝ) (jj : ℕ) =>
      let coeff := (wickCoeff k₂ l₁ jj : ℝ)
      let outTS : Fin M → ℕ × ℕ := fun m =>
        if m = j then (k₁ + k₂ - jj, l₁ + l₂ - jj)
        else ((ts1 m).1 + (ts2 m).1, (ts1 m).2 + (ts2 m).2)
      let newTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
        { support := {outTS}
          toFun := fun ts => if ts = outTS then coeff else 0
          mem_support_toFun := by
            intro ts
            simp
        }
      acc' + newTerm
    ) acc
  ) 0

/-- Wick multiplication of two normal-ordered operators.
    For each pair of terms (one from each operator), we commute the
    annihilation operators past the creation operators using the
    binomial expansion, then accumulate the results. -/
noncomputable def mul (op1 op2 : NormalOrderedOp M) : NormalOrderedOp M :=
  let resultTerms : (Fin M → ℕ × ℕ) →₀ ℝ :=
    Finset.fold (fun (acc : (Fin M → ℕ × ℕ) →₀ ℝ) (ts1 : Fin M → ℕ × ℕ) =>
      let c1 := op1.terms ts1
      Finset.fold (fun (acc' : (Fin M → ℕ × ℕ) →₀ ℝ) (ts2 : Fin M → ℕ × ℕ) =>
        let c2 := op2.terms ts2
        let newCoeff := c1 * c2
        let wick := wickTerm ts1 ts2
        -- Scale wick by newCoeff and add to accumulator
        Finset.fold (fun (acc'' : (Fin M → ℕ × ℕ) →₀ ℝ) (tsOut : Fin M → ℕ × ℕ) =>
          let coeffOut := wick tsOut
          let existing := acc''.toFun tsOut
          { acc'' with
            toFun := fun ts => if ts = tsOut then (existing + newCoeff * coeffOut) else acc''.toFun ts
            support := if (existing + newCoeff * coeffOut) = 0 then acc''.support.erase tsOut
                      else insert tsOut acc''.support
            mem_support_toFun := by
              intro ts
              by_cases hzero : (existing + newCoeff * coeffOut) = 0
              · simp [hzero]
                by_cases h_eq : ts = tsOut
                · subst h_eq; simp [hzero]
                · simp [h_eq, hzero, acc''.mem_support_toFun]
              · simp [hzero]
                by_cases h_eq : ts = tsOut
                · subst h_eq; simp [hzero]
                · simp [h_eq, hzero, acc''.mem_support_toFun]
          }
        ) acc' wick.support
      ) acc op2.terms.support
    ) 0 op1.terms.support
  { terms := resultTerms }

/-- Left-multiply by a†ᵢ (creation operator on mode i).
    Increases the creation count for mode i by 1. -/
noncomputable def mulCreation (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  { terms := op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1 + 1, (ts i).2)) }

/-- Left-multiply by aᵢ (annihilation operator on mode i).
    Increases the annihilation count for mode i by 1. -/
noncomputable def mulAnnihilation (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  { terms := op.terms.mapDomain (fun ts => Function.update ts i ((ts i).1, (ts i).2 + 1)) }

/-- Convert a `Polynomial ℝ` in variable `X i` to a `NormalOrderedOp M`.
    Uses the bosonic mapping xᵢ = (aᵢ + aᵢ†)/√2 and expands via
    the binomial theorem. -/
noncomputable def toNormalOrdered {M : ℕ} (p : Polynomial ℝ) (i : Fin M) : NormalOrderedOp M :=
  -- Express x = (a + a†)/√2, so x^n = (1/√2^n) * Σ_{j=0}^n (n choose j) * a†^j * a^(n-j)
  -- This is the normal-ordered form of a polynomial in x.
  -- For each monomial c * X^n, we produce the normal-ordered expansion
  Finset.fold (fun (acc : (Fin M → ℕ × ℕ) →₀ ℝ) (n : ℕ) =>
    let c := p n
    let xpowTerms : (Fin M → ℕ × ℕ) →₀ ℝ :=
      (Finset.range (n+1)).fold (fun (acc' : (Fin M → ℕ × ℕ) →₀ ℝ) (j : ℕ) =>
        let binomCoeff := (Nat.choose n j : ℝ)
        let totalCoeff := c * ((Real.sqrt 2)⁻¹ ^ n) * binomCoeff
        let outTS : Fin M → ℕ × ℕ := fun m =>
          if m = i then (j, n - j) else (0, 0)
        let newTerm : (Fin M → ℕ × ℕ) →₀ ℝ :=
          { support := {outTS}
            toFun := fun ts => if ts = outTS then totalCoeff else 0
            mem_support_toFun := by intro ts; simp
          }
        acc' + newTerm
      ) 0
    Finset.fold (fun (acc' : (Fin M → ℕ × ℕ) →₀ ℝ) (ts : Fin M → ℕ × ℕ) =>
      let existing := acc'.toFun ts
      let coeff := xpowTerms ts
      { acc' with
        toFun := fun t => if t = ts then (existing + coeff) else acc'.toFun t
        support := if (existing + coeff) = 0 then acc'.support.erase ts
                  else insert ts acc'.support
        mem_support_toFun := by
          intro t
          by_cases hzero : (existing + coeff) = 0
          · simp [hzero]
            by_cases h_eq : t = ts
            · subst h_eq; simp [hzero]
            · simp [h_eq, hzero, acc'.mem_support_toFun]
          · simp [hzero]
            by_cases h_eq : t = ts
            · subst h_eq; simp [hzero]
            · simp [h_eq, hzero, acc'.mem_support_toFun]
      }
    ) acc xpowTerms.support
  ) 0 p.support

/-- Differentiate a normal-ordered operator w.r.t. mode i.
    ∂/∂xᵢ (a†^k a^l) = k * a†^(k-1) a^l + l * a†^k a^(l-1)
    where the first term vanishes if k=0 and the second vanishes if l=0. -/
noncomputable def derivative (op : NormalOrderedOp M) (i : Fin M) : NormalOrderedOp M :=
  Finset.fold (fun (acc : (Fin M → ℕ × ℕ) →₀ ℝ) (ts : Fin M → ℕ × ℕ) =>
    let c := op.terms ts
    let (k, l) := ts i
    let rest : Fin M → ℕ × ℕ := fun m => if m = i then (0, 0) else ts m
    -- Term 1: k * a†^(k-1) a^l (derivative of a†^k)
    -- Term 2: l * a†^k a^(l-1) (derivative of a^l)
    let term1 : (Fin M → ℕ × ℕ) →₀ ℝ :=
      if k = 0 then 0
      else
        let outTS1 : Fin M → ℕ × ℕ := fun m =>
          if m = i then (k - 1, l) else ts m
        let newTerm1 : (Fin M → ℕ × ℕ) →₀ ℝ :=
          { support := {outTS1}
            toFun := fun t => if t = outTS1 then c * (k : ℝ) else 0
            mem_support_toFun := by
              intro t
              dsimp
              split_ifs with h_eq
              · subst h_eq; simp
              · simp
        }
        newTerm1
    let term2 : (Fin M → ℕ × ℕ) →₀ ℝ :=
      if l = 0 then 0
      else
        let outTS2 : Fin M → ℕ × ℕ := fun m =>
          if m = i then (k, l - 1) else ts m
        let newTerm2 : (Fin M → ℕ × ℕ) →₀ ℝ :=
          { support := {outTS2}
            toFun := fun t => if t = outTS2 then c * (l : ℝ) else 0
            mem_support_toFun := by
              intro t
              dsimp
              split_ifs with h_eq
              · subst h_eq; simp
              · simp
          }
        newTerm2
    -- Add both terms to accumulator
    let combined := term1 + term2
    Finset.fold (fun (acc' : (Fin M → ℕ × ℕ) →₀ ℝ) (t : Fin M → ℕ × ℕ) =>
      let existing := acc'.toFun t
      let coeff := combined t
      { acc' with
        toFun := fun tt => if tt = t then (existing + coeff) else acc'.toFun tt
        support := if (existing + coeff) = 0 then acc'.support.erase t
                  else insert t acc'.support
        mem_support_toFun := by
          intro tt
          by_cases hzero : (existing + coeff) = 0
          · simp [hzero]
            by_cases h_eq : tt = t
            · subst h_eq; simp [hzero]
            · simp [h_eq, hzero, acc'.mem_support_toFun]
          · simp [hzero]
            by_cases h_eq : tt = t
            · subst h_eq; simp [hzero]
            · simp [h_eq, hzero, acc'.mem_support_toFun]
      }
    ) acc combined.support
  ) 0 op.terms.support

/-- The number of terms in the support (for debugging). -/
def numTerms (op : NormalOrderedOp M) : ℕ :=
  op.terms.support.card
