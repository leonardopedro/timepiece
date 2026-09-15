import BookProof.ChapterSchurGershgorinGap.Part1
import BookProof.ChapterSchurGershgorinGap.Part2

/-!
# Chapter SchurGershgorinGap — the tail and coupling inputs, from matrix elements

`CONSOLIDATED_PLAN.md`, QYM-1 **task 3**: "`λ₁(H₁|core) > 0` (strict positivity, not just
non-negativity) is the mathematical claim to establish or to leave as the single named
hypothesis."

`ChapterTruncationGapLift` reduced the core form gap of the *infinite* one-particle operator
to three inputs: a gap certified on the order-`m` truncation, **tail coercivity** on
`tailSpan b m`, and a **coupling bound** across the split.  The last two were left as
hypotheses.  This chapter proves both of them from *matrix-element data* — the numbers
`aᵢⱼ = ⟪bᵢ, H bⱼ⟫` a certificate actually records — so that strict positivity of the
one-particle operator becomes a checkable family of inequalities on the entries rather than
an unanalysed assumption.

## The two criteria

* **Gershgorin (diagonal dominance) ⇒ coercivity.**  If on an index set `T` the diagonal
  entries satisfy `dᵢ ≤ Re aᵢᵢ` and the off-diagonal absolute row sums satisfy
  `∑_{j ∈ T, j ≠ i} ‖aᵢⱼ‖ ≤ rᵢ`, then on the span of `{bᵢ | i ∈ T}` the energy form obeys
  `⟪v, H v⟫ ≥ (infᵢ (dᵢ − rᵢ)) ‖v‖²` (`quadForm_ge_of_gershgorin_on`).  Taking
  `T = {i | m ≤ i}` gives exactly the tail coercivity of the lift
  (`tail_coercive_of_gershgorin`); taking `T = Set.univ` gives a core form gap outright
  (`quadForm_ge_of_gershgorin`).

* **Schur test ⇒ coupling bound.**  If the off-diagonal block `{i < m} × {m ≤ j}` has all
  row sums and all column sums at most `ε`, then `|⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split
  (`abs_inner_block_le`, `coupling_bound_of_schur`) — the second hypothesis of the lift.

Both criteria are stated with the sums quantified over *arbitrary finite subsets* of the
index set, which is the form a summable row / column bound delivers and which keeps every
proof finite.

## Deliverables

* `bvec`, `entry` — the basis vectors as core elements and the matrix elements;
* `exists_repr_of_mem_span_image`, `norm_sq_sum`, `quadForm_sum`, `inner_sum_apply_sum` —
  the finite-combination calculus behind everything else;
* **`quadForm_sum_ge`**, **`quadForm_ge_of_gershgorin_on`**, `quadForm_ge_of_gershgorin`,
  **`tail_coercive_of_gershgorin`**;
* **`abs_inner_block_le`**, `coupling_bound_of_schur`;
* **`gap_of_level_gap_and_matrix_bounds`** — the composition with
  `TruncationGapLift.gap_of_level_gap_and_tail`: certified order-`m` gap + Gershgorin tail
  data + Schur block data ⇒ core form gap `μ − ε`, and `strict_pos_of_matrix_bounds` — the
  strict positivity `⟪v, H v⟫ > 0` for `v ≠ 0` when `ε < μ`, which is QYM-1 task 3's claim
  in the form the chain consumes;
* **`ym_fock_gap_of_truncated_gap_and_matrix_bounds`** and
  **`ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds`** — the same for the concrete
  gauge-fixed Yang–Mills one-particle Hamiltonian and its `dΓ` lift.

## Honest boundary

What is proved here is the *implication*: the recorded matrix elements satisfying diagonal
dominance on the tail and a Schur bound on the coupling block give the gap, with the
explicit constant `μ − ε`.  Whether the gauge-fixed Yang–Mills entries satisfy those
inequalities is not decided here — it is a computation on the entries, not an assumption
about the spectrum, which is the point: the remaining input is now finite, checkable data
of the same kind the certificate already reports.  No mass gap of the physical Yang–Mills
Hamiltonian is claimed.

Everything in this module is `sorry`-free and `axiom`-free.
-/
