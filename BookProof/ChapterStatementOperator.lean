import BookProof.Prelude

/-!
# Statements as operators on the Hilbert space of models

`book.tex`, chapter *Statistical Model Theory and Bayesian priors where the Riemann
Hypothesis is true*, §*Statistical Model Theory*:

> Then, we can represent statements (theorems if proven so) as operators in a Hilbert
> space.  This allows to deal with undecidable statements as projection operators, which
> project the Hilbert space of models to a smaller subspace.  Statements become more than
> true/false/undecidable … We can even consider uncertain statements, that are operators
> but not projections. … an undecidable statement also has a proof and "approximated"
> proofs (which evaluate incorrectly for a small subspace of the models).

This chapter formalizes that calculus.  `H` is the Hilbert space of models; a
`ModelStatement` is an orthogonal projection on it, and its *truth value* on a model
vector `ψ` is the expectation `Re ⟪ψ, Pψ⟫`.

Main results.

* `ModelStatement.truthValue_eq_norm_sq`, `truthValue_nonneg`, `truthValue_le_norm_sq`,
  `truthValue_mem_unitInterval` — the truth value is a real number between `0` and
  `‖ψ‖²`, so on unit model vectors it is a number in `[0,1]`: "statements become more
  than true/false/undecidable".
* `ModelStatement.truthValue_not` — negation `1 - P` complements the truth value.
* `ModelStatement.and` — the conjunction of two *commuting* statements is again a
  statement, and it is weaker than each conjunct (`truthValue_and_le_left`/`_right`).
* `ModelStatement.truthValue_eq_zero_iff` and `truthValue_eq_norm_sq_iff` — the models
  of extreme truth value are exactly those killed by, respectively fixed by, the
  projection.
* `ModelStatement.undecidable_iff` — a statement is undecidable (`P ≠ 0` and `P ≠ 1`)
  exactly when there is a nonzero model where it holds outright and a nonzero model
  where it fails outright: the projection has a proper nonzero range.
* `UncertainStatement` — the weaker notion the book asks for: a self-adjoint operator
  with truth values in `[0, ‖ψ‖²]`, not required to be a projection.
  `ModelStatement.toUncertain` embeds the projections and
  `halfUncertain_not_idempotent` exhibits an uncertain statement that is genuinely not a
  projection.
* `approximate_proof_error` — an "approximated proof": an operator within `ε` of the
  statement evaluates every model to within `ε‖ψ‖²` of the true value.
-/

namespace BookProof.ChapterStatementOperator

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **statement** about the models collected in the Hilbert space `H`: an orthogonal
projection, i.e. a self-adjoint idempotent bounded operator.  Its range is the subspace
of models in which the statement holds. -/
structure ModelStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The operator representing the statement. -/
  op : H →L[ℂ] H
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint op
  /-- The operator is idempotent. -/
  isIdempotent : op ∘L op = op

namespace ModelStatement

variable (S : ModelStatement H) (ψ : H)

/-- The **truth value** of the statement on the model vector `ψ`: the expectation
`Re ⟪ψ, Pψ⟫`. -/
noncomputable def truthValue : ℝ := RCLike.re (inner ℂ ψ (S.op ψ))

/-- The truth value is the squared norm of the projected model. -/
@[simp] theorem truthValue_eq_norm_sq : S.truthValue ψ = ‖S.op ψ‖ ^ 2 := by
  have h1 : (inner ℂ ψ (S.op ψ) : ℂ) = inner ℂ ψ (S.op (S.op ψ)) := by
    rw [← ContinuousLinearMap.comp_apply, S.isIdempotent]
  rw [truthValue, h1, ← ContinuousLinearMap.adjoint_inner_left, S.isSelfAdjoint.adjoint_eq,
    inner_self_eq_norm_sq]

theorem truthValue_nonneg : 0 ≤ S.truthValue ψ := by
  rw [S.truthValue_eq_norm_sq]; positivity

/-- A projection does not increase norms. -/
theorem norm_op_le : ‖S.op ψ‖ ≤ ‖ψ‖ := by
  have hb : ‖S.op ψ‖ ^ 2 = RCLike.re (inner ℂ ψ (S.op ψ)) := (S.truthValue_eq_norm_sq ψ).symm
  have h1 : RCLike.re (inner ℂ ψ (S.op ψ)) ≤ ‖(inner ℂ ψ (S.op ψ) : ℂ)‖ :=
    le_trans (le_abs_self _) (RCLike.abs_re_le_norm _)
  have h2 : ‖(inner ℂ ψ (S.op ψ) : ℂ)‖ ≤ ‖ψ‖ * ‖S.op ψ‖ := norm_inner_le_norm ψ (S.op ψ)
  rcases eq_or_lt_of_le (norm_nonneg (S.op ψ)) with h | h
  · rw [← h]; exact norm_nonneg ψ
  · have hsq : ‖S.op ψ‖ ^ 2 ≤ ‖ψ‖ * ‖S.op ψ‖ := hb ▸ (h1.trans h2)
    nlinarith

theorem truthValue_le_norm_sq : S.truthValue ψ ≤ ‖ψ‖ ^ 2 := by
  rw [S.truthValue_eq_norm_sq]
  have := S.norm_op_le ψ
  nlinarith [norm_nonneg (S.op ψ), norm_nonneg ψ]

/-- On a unit model vector the truth value lies in `[0,1]`. -/
theorem truthValue_mem_unitInterval (hψ : ‖ψ‖ = 1) :
    S.truthValue ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨S.truthValue_nonneg ψ, by simpa [hψ] using S.truthValue_le_norm_sq ψ⟩

/-- The **negation** of a statement. -/
def not (S : ModelStatement H) : ModelStatement H where
  op := 1 - S.op
  isSelfAdjoint := by
    simpa using (IsSelfAdjoint.one (R := H →L[ℂ] H)).sub S.isSelfAdjoint
  isIdempotent := by
    have hmul : S.op * S.op = S.op := S.isIdempotent
    change (1 - S.op) * (1 - S.op) = 1 - S.op
    have h : (1 - S.op) * (1 - S.op) = 1 - S.op - S.op + S.op * S.op := by noncomm_ring
    rw [h, hmul]; abel

@[simp] theorem not_op : S.not.op = 1 - S.op := rfl

/-- Truth values of a statement and its negation are complementary. -/
theorem truthValue_not : S.not.truthValue ψ = ‖ψ‖ ^ 2 - S.truthValue ψ := by
  simp [truthValue, not_op, inner_sub_right, ← Complex.ofReal_pow]

/-- The **conjunction** of two commuting statements. -/
def and (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    ModelStatement H where
  op := S.op ∘L T.op
  isSelfAdjoint := by
    have hadj : adjoint (S.op ∘L T.op) = T.op ∘L S.op := by
      rw [ContinuousLinearMap.adjoint_comp, S.isSelfAdjoint.adjoint_eq,
        T.isSelfAdjoint.adjoint_eq]
    rw [IsSelfAdjoint, star_eq_adjoint, hadj, ← hcomm]
  isIdempotent := by
    have hS : S.op * S.op = S.op := S.isIdempotent
    have hT : T.op * T.op = T.op := T.isIdempotent
    have hc : S.op * T.op = T.op * S.op := hcomm
    change (S.op * T.op) * (S.op * T.op) = S.op * T.op
    calc (S.op * T.op) * (S.op * T.op) = S.op * (T.op * S.op) * T.op := by noncomm_ring
      _ = S.op * (S.op * T.op) * T.op := by rw [← hc]
      _ = (S.op * S.op) * (T.op * T.op) := by noncomm_ring
      _ = S.op * T.op := by rw [hS, hT]

@[simp] theorem and_op (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).op = S.op ∘L T.op := rfl

theorem truthValue_and_le_left (S T : ModelStatement H)
    (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).truthValue ψ ≤ S.truthValue ψ := by
  rw [truthValue_eq_norm_sq, truthValue_eq_norm_sq, and_op]
  have h : S.op (T.op ψ) = T.op (S.op ψ) := by
    simpa using congrArg (fun A : H →L[ℂ] H => A ψ) hcomm
  have hle : ‖S.op (T.op ψ)‖ ≤ ‖S.op ψ‖ := by
    rw [h]; exact T.norm_op_le (S.op ψ)
  simpa using pow_le_pow_left₀ (norm_nonneg (S.op (T.op ψ))) hle 2

theorem truthValue_and_le_right (S T : ModelStatement H)
    (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).truthValue ψ ≤ T.truthValue ψ := by
  rw [truthValue_eq_norm_sq, truthValue_eq_norm_sq, and_op]
  have hle : ‖S.op (T.op ψ)‖ ≤ ‖T.op ψ‖ := S.norm_op_le (T.op ψ)
  simpa using pow_le_pow_left₀ (norm_nonneg (S.op (T.op ψ))) hle 2

/-- The models in which the statement holds outright are exactly those of maximal truth
value. -/
theorem truthValue_eq_norm_sq_iff : S.truthValue ψ = ‖ψ‖ ^ 2 ↔ S.op ψ = ψ := by
  constructor
  · intro h
    have hre : RCLike.re (inner ℂ ψ (S.op ψ)) = ‖S.op ψ‖ ^ 2 := S.truthValue_eq_norm_sq ψ
    have hsq : ‖S.op ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by rw [← S.truthValue_eq_norm_sq ψ, h]
    have hz : ‖ψ - S.op ψ‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), hre, hsq]; ring
    have hzero : ψ - S.op ψ = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz)
    exact (sub_eq_zero.mp hzero).symm
  · intro h; rw [S.truthValue_eq_norm_sq, h]

/-- The models in which the statement fails outright are exactly those of zero truth
value. -/
theorem truthValue_eq_zero_iff : S.truthValue ψ = 0 ↔ S.op ψ = 0 := by
  rw [S.truthValue_eq_norm_sq]
  constructor
  · intro h
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · intro h; rw [h]; simp

/-- A statement is **undecidable** when its operator is neither `0` nor `1`: it projects
the space of models onto a proper nonzero subspace. -/
def Undecidable (S : ModelStatement H) : Prop := S.op ≠ 0 ∧ S.op ≠ 1

/-- Undecidability, spelled out on models: there is a nonzero model in which the
statement holds outright, and a nonzero model in which it fails outright. -/
theorem undecidable_iff :
    S.Undecidable ↔ (∃ a : H, a ≠ 0 ∧ S.op a = a) ∧ (∃ b : H, b ≠ 0 ∧ S.op b = 0) := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · obtain ⟨x, hx⟩ : ∃ x : H, S.op x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h0 (ContinuousLinearMap.ext hcon)
      refine ⟨S.op x, hx, ?_⟩
      rw [← ContinuousLinearMap.comp_apply, S.isIdempotent]
    · obtain ⟨x, hx⟩ : ∃ x : H, S.op x ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact h1 (ContinuousLinearMap.ext (by simpa using hcon))
      refine ⟨x - S.op x, sub_ne_zero.mpr (fun h => hx (h ▸ rfl)), ?_⟩
      have hmap : S.op (x - S.op x) = S.op x - S.op (S.op x) := by simp
      rw [hmap, ← ContinuousLinearMap.comp_apply, S.isIdempotent, sub_self]
  · rintro ⟨⟨a, ha, hae⟩, ⟨b, hb, hbe⟩⟩
    refine ⟨fun h => ha ?_, fun h => hb ?_⟩
    · rw [← hae, h]; simp
    · rw [← hbe, h]; simp

end ModelStatement

/-- An **uncertain statement**: the book's weakening — a self-adjoint operator whose
expectation on every model lies between `0` and `‖ψ‖²`, but which need not be a
projection. -/
structure UncertainStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The operator representing the uncertain statement. -/
  op : H →L[ℂ] H
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint op
  /-- Expectations are nonnegative. -/
  nonneg : ∀ ψ : H, 0 ≤ RCLike.re (inner ℂ ψ (op ψ))
  /-- Expectations are bounded by the squared norm. -/
  le_norm_sq : ∀ ψ : H, RCLike.re (inner ℂ ψ (op ψ)) ≤ ‖ψ‖ ^ 2

/-- Every statement is in particular an uncertain statement. -/
noncomputable def ModelStatement.toUncertain (S : ModelStatement H) :
    UncertainStatement H where
  op := S.op
  isSelfAdjoint := S.isSelfAdjoint
  nonneg := fun ψ => S.truthValue_nonneg ψ
  le_norm_sq := fun ψ => S.truthValue_le_norm_sq ψ

omit [CompleteSpace H] in
/-- The expectation of `½ · 1` is half the squared norm. -/
theorem half_inner_eq (ψ : H) :
    RCLike.re (inner ℂ ψ (((1 / 2 : ℂ) • (1 : H →L[ℂ] H)) ψ)) = ‖ψ‖ ^ 2 / 2 := by
  simp [inner_smul_right, ← Complex.ofReal_pow]
  ring

/-- The "half true" statement `½ · 1`: an uncertain statement. -/
noncomputable def halfUncertain : UncertainStatement H where
  op := (1 / 2 : ℂ) • (1 : H →L[ℂ] H)
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_smul, star_one]
    norm_num
  nonneg := fun ψ => by rw [half_inner_eq]; positivity
  le_norm_sq := fun ψ => by
    rw [half_inner_eq]
    nlinarith [sq_nonneg ‖ψ‖]

@[simp] theorem halfUncertain_op :
    (halfUncertain (H := H)).op = (1 / 2 : ℂ) • (1 : H →L[ℂ] H) := rfl

/-- `halfUncertain` really is *not* a projection, as soon as there is a nonzero model:
the book's "operators but not projections". -/
theorem halfUncertain_not_idempotent (h : ∃ ψ : H, ψ ≠ 0) :
    ¬ ((halfUncertain (H := H)).op ∘L (halfUncertain (H := H)).op
        = (halfUncertain (H := H)).op) := by
  obtain ⟨ψ, hψ⟩ := h
  intro hcon
  rw [halfUncertain_op] at hcon
  have happ := congrArg (fun A : H →L[ℂ] H => A ψ) hcon
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul] at happ
  have h4 : ((1 / 2 : ℂ) * (1 / 2) - (1 / 2 : ℂ)) • ψ = 0 := by
    rw [sub_smul, sub_eq_zero]; exact happ
  rcases smul_eq_zero.mp h4 with h1 | h0
  · norm_num at h1
  · exact hψ h0

/-- An **approximated proof**: an operator `A` within `ε` of the statement's projection
evaluates every model to within `ε‖ψ‖²` of the true value — it "evaluates incorrectly
only for a small subspace of the models". -/
theorem approximate_proof_error (S : ModelStatement H) (A : H →L[ℂ] H) (ε : ℝ)
    (hA : ‖A - S.op‖ ≤ ε) (ψ : H) :
    |RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ| ≤ ε * ‖ψ‖ ^ 2 := by
  have hdiff : RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ
      = RCLike.re (inner ℂ ψ ((A - S.op) ψ)) := by
    simp [ModelStatement.truthValue, inner_sub_right]
  rw [hdiff]
  have h1 := RCLike.abs_re_le_norm (inner ℂ ψ ((A - S.op) ψ))
  have h2 : ‖(inner ℂ ψ ((A - S.op) ψ) : ℂ)‖ ≤ ‖ψ‖ * ‖(A - S.op) ψ‖ := norm_inner_le_norm _ _
  have h3 : ‖(A - S.op) ψ‖ ≤ ε * ‖ψ‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hA (norm_nonneg ψ))
  calc |RCLike.re (inner ℂ ψ ((A - S.op) ψ))| ≤ ‖ψ‖ * ‖(A - S.op) ψ‖ := le_trans h1 h2
    _ ≤ ‖ψ‖ * (ε * ‖ψ‖) := mul_le_mul_of_nonneg_left h3 (norm_nonneg ψ)
    _ = ε * ‖ψ‖ ^ 2 := by ring

end BookProof.ChapterStatementOperator
