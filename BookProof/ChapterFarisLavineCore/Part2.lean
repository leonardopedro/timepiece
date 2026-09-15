import BookProof.Prelude
import BookProof.ChapterFarisLavineCore.Part1

/-!
# The Faris–Lavine commutator criterion for essential self-adjointness

This module formalizes and **proves** the abstract theorem of

> W. G. Faris and R. B. Lavine, *Commutators and self-adjointness of Hamiltonian
> operators*, Commun. Math. Phys. **35** (1974), 39–48, Theorem 1,

which elsewhere in this project (`BookProof.ChapterNavierStokesFlow`) had to be
carried as a named hypothesis.  The statement of the paper is:

> Let `H` be a Hermitian operator and `N ≥ 0` a positive self-adjoint operator
> with (i) `𝒟(N) ⊆ 𝒟(H)` and (ii) `± i[H, N] ≤ c N` for some `c < ∞`.  Then `H`
> is essentially self-adjoint.

## How the statement is rendered here

* The Hilbert space is a complex inner-product space `F` which is complete.
* `H` and `N` are linear maps `D →ₗ[ℂ] F` on a common domain `D`, which plays the
  role of `𝒟(N)`; hypothesis (i) of the paper is built into this — `H` is defined
  wherever `N` is.  (The conclusion is about the restriction of `H` to `𝒟(N)`,
  which by the last remark of §2 of the paper is the stronger statement: any
  symmetric extension of an essentially self-adjoint operator has the same
  closure.)
* Symmetry is `SymmetricOn`, the quadratic form of `N` is `quadForm`, and
  `commForm H N x = ⟪x, i[H, N] x⟫` is the commutator form; that this is a real
  number is `commForm_eq`.  Hypothesis (ii) is `|commForm H N x| ≤ c * quadForm N x`,
  which is exactly the two-sided bound `± i[H, N] ≤ c N` of the paper.
* Essential self-adjointness is rendered, as everywhere in this project, by the
  vanishing of the deficiency spaces of the adjoint: `EssentiallySelfAdjointOn D H`
  says that no `w ≠ 0` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D`.
* Self-adjointness of `N` is used in the paper at exactly one place: it makes
  `N + 1` a bijection of `𝒟(N)` onto the whole space, so that `(N+1)⁻¹ f` is an
  admissible test vector.  That consequence — surjectivity of `N + 1` — is what
  is assumed here (`hNsurj`), so no spectral theory for unbounded operators is
  needed and the criterion applies verbatim to any `N` for which `-1` is in the
  resolvent set.

## Contents

* `deficiencyTrivialAt_of_farisLavine` — the computation of the paper: under the
  Faris–Lavine hypotheses the deficiency space at `d i` vanishes whenever
  `2|d| > c`.  This is the displayed inequality `± 2 d ⟪f, N⁻¹f⟫ ≤ c ⟪f, N⁻¹f⟫`
  of the original proof.
* `exists_weak_graph_limit` — the closure of a symmetric operator with dense
  range of `H - d i` hits every vector: given `y`, there are `u, z` in the closure
  of the graph with `z - d i u = y`.  Proved by hand from the identity
  `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²`, which makes the approximating sequence and
  its image Cauchy.
* `deficiencyTrivialAt_of_dense_range` — the classical basic criterion: for a
  symmetric operator, vanishing of the deficiency spaces at one conjugate pair
  `± d i` (`d ≠ 0`) forces vanishing at *every* non-real point.  This is the step
  that upgrades the paper's "for `|d|` large" to essential self-adjointness.
* `essentiallySelfAdjointOn_of_farisLavine` — **Theorem 1 of Faris–Lavine.**
* `hasZeroDeficiencyOn_of_farisLavine` — the same conclusion in the predicate
  `BookProof.NavierStokesFlow.HasZeroDeficiencyOn` used by the Navier–Stokes
  chapters, for an operator that leaves its domain invariant.
* `not_farisLavine_criterion_of_relative_bound` — a caveat, and the reason the
  hypotheses above are what they are: the *unrestricted* form of the criterion
  (relative bound `‖Hv‖ ≤ a‖Nv‖` plus commutator bound, with no positivity and no
  self-adjointness required of `N`) is **false**; taking `N = H` for the
  limit-circle Jacobi operator of `BookProof.ChapterNavierStokesDeficiency`
  satisfies both inequalities while essential self-adjointness fails.
* `essentiallySelfAdjointOn_of_bounded_symmetric` and
  `multiplication_essentiallySelfAdjoint` — the hypotheses are satisfiable: the
  first in the everywhere-defined case, the second for the (unbounded)
  multiplication operator by an arbitrary real sequence on its maximal domain in
  `ℓ²(ℕ)`.

Nothing here is assumed: the module contains no `axiom`, and every result is
proved from Mathlib.
-/

namespace BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
/-! ## Theorem 1 of Faris–Lavine -/

/-- **Theorem 1 (Faris–Lavine 1974).**  Let `H` be a Hermitian operator and `N`
a positive operator on a common dense domain `D` of a Hilbert space, such that

* `± i[H, N] ≤ c N` as quadratic forms on `D` (hypothesis (ii) of the paper), and
* `N + 1` maps `D` onto the whole space — the one consequence of "`N ≥ 0` is
  self-adjoint" that the argument uses.

Then `H` is essentially self-adjoint: both deficiency spaces of its adjoint
vanish.

Hypothesis (i) of the paper, `𝒟(N) ⊆ 𝒟(H)`, is built into the statement by
giving `H` and `N` the same domain; the conclusion is about the restriction of
`H` to `𝒟(N)`, which is the sharper statement.  Density of `D` is not needed as a
hypothesis: it follows from surjectivity of `N + 1`. -/
theorem essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine H N c d hH hN hc hNpos hNsurj hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine H N c (-d) hH hN hc hNpos hNsurj hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

/-- The everywhere-defined case, as a sanity check that the hypotheses of
Theorem 1 are satisfiable: take `N = 1`, whose commutator with anything vanishes.
A bounded (indeed any) symmetric operator defined on the whole space is
essentially self-adjoint. -/
theorem essentiallySelfAdjointOn_top_of_symmetric [CompleteSpace F]
    (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hH : SymmetricOn ⊤ H) :
    EssentiallySelfAdjointOn (⊤ : Submodule ℂ F) H := by
  refine essentiallySelfAdjointOn_of_farisLavine H (⊤ : Submodule ℂ F).subtype 0 hH
    (fun x y => rfl) le_rfl (fun x => ?_)
    (fun f => ⟨⟨(2 : ℂ)⁻¹ • f, trivial⟩, ?_⟩) (fun x => ?_)
  · have hq : quadForm (⊤ : Submodule ℂ F).subtype x = ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, Submodule.subtype_apply]
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    rw [hq]; positivity
  · change (2 : ℂ)⁻¹ • f + (2 : ℂ)⁻¹ • f = f
    rw [← add_smul]
    norm_num
  · have h : (inner ℂ (H x) ((⊤ : Submodule ℂ F).subtype x) : ℂ).im = 0 :=
      inner_apply_self_im H hH x
    rw [commForm_eq, h]
    simp

/-! ## Corollary 1.1: the criterion on a core

The paper's Corollary 1.1 weakens the hypotheses to a linear subspace `C` which
is a core: the estimates are only required on `C`, and the conclusion is that the
restriction of `H` to `C` is already essentially self-adjoint.  Here the core
property is stated as it is used — every vector of `𝒟(N)` is approximated by
vectors of `C` *together with* their images under `N` (the graph norm of `N`) —
and the relative bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` transports the approximation from
the graph of `N` to the graph of `H`. -/

/-- If every vector of the domain `D` is approximated, in the graph norm of `H`,
by vectors of a subspace `C ≤ D`, then a deficiency vector for the restriction of
`H` to `C` is one for `H` itself.  (Restricting an operator can only enlarge its
deficiency spaces; a core is exactly what makes the enlargement trivial.) -/
theorem essentiallySelfAdjointOn_restrict_of_graph_core
    {C : Submodule ℂ F} (hCD : C ≤ D) (H : D →ₗ[ℂ] F)
    (hcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖H y - H x‖ < ε)
    (hdef : EssentiallySelfAdjointOn D H) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  have main : ∀ σ : ℂ, DeficiencyTrivialAt D H σ →
      DeficiencyTrivialAt C (H.comp (Submodule.inclusion hCD)) σ := by
    intro σ hσ w hw
    refine hσ w fun x => ?_
    have hzero : ∀ ε : ℝ, 0 < ε →
        ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
      intro ε hε
      obtain ⟨y, hyC, hy1, hy2⟩ := hcore x ε hε
      have hwy := hw ⟨(y : F), hyC⟩
      have hHy : (H.comp (Submodule.inclusion hCD)) ⟨(y : F), hyC⟩ = H y := by
        simp only [LinearMap.comp_apply]
        congr 1
      rw [hHy] at hwy
      have hsplit : (inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w
          = (inner ℂ (H x - H y) w : ℂ) + σ * inner ℂ ((y : F) - (x : F)) w := by
        rw [inner_sub_left, inner_sub_left, hwy]
        push_cast
        ring
      calc ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖
          ≤ ‖(inner ℂ (H x - H y) w : ℂ)‖ + ‖σ * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖H x - H y‖ * ‖w‖ + ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
            gcongr
            · exact norm_inner_le_norm _ _
            · rw [norm_mul]
              gcongr
              exact norm_inner_le_norm _ _
        _ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
            have h1 : ‖H x - H y‖ ≤ ε := by
              rw [← norm_neg]; simpa [neg_sub] using hy2.le
            have h2 : ‖(y : F) - (x : F)‖ ≤ ε := hy1.le
            have hA : ‖H x - H y‖ * ‖w‖ ≤ ε * ‖w‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
            have hB : ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖σ‖ * (ε * ‖w‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
                (norm_nonneg σ)
            have hsum : ε * ‖w‖ + ‖σ‖ * (ε * ‖w‖) = ε * (1 + ‖σ‖) * ‖w‖ := by ring
            linarith
    have hnn : ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos : 0 < δ / ((1 + ‖σ‖) * (1 + ‖w‖)) := by positivity
      have := hzero _ hpos
      have hbound : δ / ((1 + ‖σ‖) * (1 + ‖w‖)) * (1 + ‖σ‖) * ‖w‖ ≤ δ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, norm_nonneg σ, hδ.le]
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)
  exact ⟨main _ hdef.1, main _ hdef.2⟩

/-- **Corollary 1.1 of Faris–Lavine.**  The Faris–Lavine hypotheses on `𝒟(N)`,
together with the relative bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` and a subspace `C` that
is a core for `N` (approximation in the graph norm of `N`), give essential
self-adjointness of the restriction of `H` to `C`. -/
theorem essentiallySelfAdjointOn_core_of_farisLavine [CompleteSpace F]
    {C : Submodule ℂ F} (hCD : C ≤ D) (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hrel : ∀ x : D, ‖H x‖ ^ 2 ≤ a * ‖N x‖ ^ 2 + b * ‖(x : F)‖ ^ 2)
    (hNcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖N y - N x‖ < ε) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  refine essentiallySelfAdjointOn_restrict_of_graph_core hCD H (fun x ε hε => ?_)
    (essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm)
  set K : ℝ := |a| + |b| + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min ε (ε / Real.sqrt K) with hδ
  have hδpos : 0 < δ := by
    refine lt_min hε ?_
    positivity
  obtain ⟨y, hyC, hy1, hy2⟩ := hNcore x δ hδpos
  refine ⟨y, hyC, lt_of_lt_of_le hy1 (min_le_left _ _), ?_⟩
  have hdiff : H y - H x = H (y - x) := by rw [map_sub]
  have hNdiff : N y - N x = N (y - x) := by rw [map_sub]
  have hcoe : ((y - x : D) : F) = (y : F) - (x : F) := rfl
  have hsq := hrel (y - x)
  rw [← hdiff, ← hNdiff, hcoe] at hsq
  have hb1 : ‖N y - N x‖ ≤ δ := hy2.le
  have hb2 : ‖(y : F) - (x : F)‖ ≤ δ := hy1.le
  have hδK : δ ^ 2 * K ≤ ε ^ 2 := by
    have h1 : δ ≤ ε / Real.sqrt K := min_le_right _ _
    have hsqrt : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKpos.le
    have hsqrtpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKpos
    have h2 : δ * Real.sqrt K ≤ ε := by
      rw [le_div_iff₀ hsqrtpos] at h1
      exact h1
    have h3 : (δ * Real.sqrt K) ^ 2 ≤ ε ^ 2 := by
      nlinarith [mul_nonneg hδpos.le hsqrtpos.le]
    calc δ ^ 2 * K = (δ * Real.sqrt K) ^ 2 := by rw [mul_pow, hsqrt]
      _ ≤ ε ^ 2 := h3
  have hfinal : ‖H y - H x‖ ^ 2 < ε ^ 2 := by
    have hnn1 : 0 ≤ ‖N y - N x‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖(y : F) - (x : F)‖ := norm_nonneg _
    have hle : a * ‖N y - N x‖ ^ 2 + b * ‖(y : F) - (x : F)‖ ^ 2 ≤ (|a| + |b|) * δ ^ 2 := by
      have hs1 : ‖N y - N x‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have hs2 : ‖(y : F) - (x : F)‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have ha : a * ‖N y - N x‖ ^ 2 ≤ |a| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self a, sq_nonneg ‖N y - N x‖])
          (mul_le_mul_of_nonneg_left hs1 (abs_nonneg a))
      have hbb : b * ‖(y : F) - (x : F)‖ ^ 2 ≤ |b| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self b, sq_nonneg ‖(y : F) - (x : F)‖])
          (mul_le_mul_of_nonneg_left hs2 (abs_nonneg b))
      linarith
    have hstrict : (|a| + |b|) * δ ^ 2 < ε ^ 2 := by
      have : δ ^ 2 * K = (|a| + |b|) * δ ^ 2 + δ ^ 2 := by rw [hK]; ring
      nlinarith [pow_pos hδpos 2]
    linarith
  have hεpos : (0 : ℝ) < ε := hε
  nlinarith [norm_nonneg (H y - H x)]

end BookProof.FarisLavine
