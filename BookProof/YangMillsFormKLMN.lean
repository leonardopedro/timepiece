import BookProof.YangMillsFormClosureNonDiagonal

/-!
# §23 The KLMN theorem at relative bound `a < 1`, for diagonal forms

`YangMillsFormClosureNonDiagonal` §21 represents the sum form `q_c + q_K` by a self-adjoint
operator **when `K` is bounded** — relative bound `a = 0`.  §5–§6 of `YangMillsFormClosure` record
that the interacting theory does not stay in that branch: the magnetic term has no uniform norm
bound as the cut-off is removed, only a relative *form* bound with `a < 1`.  This section closes
that gap for the forms the chapter models, i.e. for diagonal symbols.

The content of the KLMN theorem, in the diagonal case, is four statements, and all four are proved
here:

* **the form domain is closed** — `formENN_le_of_tendsto`: if `x k → y` in `L²` and the form norms
  `‖x k‖_c` are bounded by `M`, then `y` is in the form domain and `‖y‖_c ≤ M`.  This is Fatou's
  lemma on the monotone partial sums of the sign-free series, and it is where the closedness of a
  diagonal form comes from (`formTsum_lsc` for the real series, `formDom_of_tendsto`);
* **relative boundedness is form boundedness with the same constant** — a symbol `b` with
  `|b n| ≤ a c n + β` is `q_c`-form bounded, so the *sum* form is finite exactly where `q_c` is:
  `formDom_add_of_relativeBound` (one inclusion) and `formDom_of_relativeBound_add` (the other,
  which uses `a < 1`);
* **the sum is bounded below by `(1 − a)θ − β`** on the whole form domain
  (`formSum_ge_formDom`), not only on the operator domain where §21 reads it;
* **it is the quadratic form of the self-adjoint operator** `diagUnb (c + b)`
  (`klmn_selfAdjoint`, `klmn_form_eq_inner`), whose domain is contained in the unperturbed form
  domain (`klmn_formDom_of_operatorDomain`).

So for the diagonal models the KLMN theorem is no longer conditional on an operator-level relative
bound: the `a < 1` branch is a theorem about the form itself.  What is *not* claimed is the
instantiation for the momentum-representation magnetic ladder — that is the identification question
of §22's caveat, not a question about forms.

## Contents

* `formNN`, `formENN` — the form norm squared, `∑ |c n| ‖x n‖²`, as an `ℝ≥0`/`ℝ≥0∞` series;
* `formENN_ne_top_iff` — finiteness of that series *is* the form domain `formDom`;
* **`formENN_le_of_tendsto`** — lower semicontinuity in the `L²` topology;
* **`formTsum_lsc`**, **`formDom_of_tendsto`** — the same for the real form series, which is the
  closedness of the diagonal form;
* **`formDom_add_of_relativeBound`**, **`formDom_of_relativeBound_add`** — the KLMN form-domain
  equality;
* **`formSum_ge_formDom`** — the KLMN lower bound on the form domain;
* `klmn_selfAdjoint`, `klmn_form_eq_inner`, `klmn_formDom_of_operatorDomain`,
  **`klmn`** — the self-adjoint operator whose quadratic form is the sum form.
-/

noncomputable section

namespace BookProof.YangMillsFormClosureND

open scoped NNReal ENNReal

open BookProof.YangMillsFormClosure BookProof.ChapterUnitaryTransport

open Filter Topology

variable {d : ℕ}

/-! ## 23. The KLMN theorem for diagonal forms -/

/-- The sign-free form series, term by term: `|c n| ‖x n‖²` as a nonnegative real. -/
def formNN (c : Idx d → ℝ) (x : L2 d) (n : Idx d) : ℝ≥0 :=
  ⟨|c n| * ‖x n‖ ^ 2, mul_nonneg (abs_nonneg (c n)) (sq_nonneg (‖x n‖))⟩

@[simp] theorem coe_formNN (c : Idx d → ℝ) (x : L2 d) (n : Idx d) :
    ((formNN c x n : ℝ≥0) : ℝ) = |c n| * ‖x n‖ ^ 2 := rfl

/-- **The form norm squared as an `ℝ≥0∞` series**: `∑' |c n| ‖x n‖²`.  It is finite exactly on the
form domain, and being a supremum of finite partial sums it is lower semicontinuous for free. -/
noncomputable def formENN (c : Idx d → ℝ) (x : L2 d) : ℝ≥0∞ :=
  ∑' n : Idx d, (formNN c x n : ℝ≥0∞)

/-- The two forms of the term: the `ℝ≥0` coercion and `ofReal` agree. -/
theorem ENN_formNN (c : Idx d → ℝ) (x : L2 d) (n : Idx d) :
    ((formNN c x n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (|c n| * ‖x n‖ ^ 2) :=
  (ENNReal.ofReal_eq_coe_nnreal
    (mul_nonneg (abs_nonneg (c n)) (sq_nonneg (‖x n‖)))).symm

/-- **Finiteness of the form norm is the form domain.** -/
theorem formENN_ne_top_iff {c : Idx d → ℝ} {x : L2 d} : formENN c x ≠ ∞ ↔ formDom c x :=
  (ENNReal.tsum_coe_ne_top_iff_summable (f := formNN c x)).trans
    (NNReal.summable_coe (f := formNN c x)).symm

theorem formDom_iff_formENN_ne_top {c : Idx d → ℝ} {x : L2 d} :
    formDom c x ↔ formENN c x ≠ ∞ :=
  formENN_ne_top_iff.symm

/-- The form norm is monotone in the symbol, on the form domain. -/
theorem formENN_mono {c c' : Idx d → ℝ} {x : L2 d} (h : ∀ n, |c n| ≤ |c' n|) :
    formENN c x ≤ formENN c' x :=
  ENNReal.tsum_le_tsum fun n => by
    refine ENNReal.coe_le_coe.2 ?_
    exact mul_le_mul_of_nonneg_right (h n) (sq_nonneg _)

/-- **Lower semicontinuity of the diagonal form.**  If `x k → y` in `L²` and the form norms are
bounded by `M`, then the form norm of the limit is at most `M`.  The proof is Fatou's lemma in the
shape the `ℝ≥0∞` series gives it: the form norm is the supremum of its finite partial sums, each of
which is a finite sum of continuous functions of `x`. -/
theorem formENN_le_of_tendsto {c : Idx d → ℝ} {x : ℕ → L2 d} {y : L2 d}
    (hx : Tendsto x atTop (𝓝 y)) {M : ℝ≥0∞} (hM : ∀ k, formENN c (x k) ≤ M) :
    formENN c y ≤ M := by
  have hcoord : ∀ n : Idx d, Tendsto (fun k => (x k : L2 d) n) atTop (𝓝 (y n)) := by
    intro n
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hsub : Tendsto (fun k => ‖x k - y‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hx
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hsub
    filter_upwards with k
    have h := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x k - y) n
    simpa only [lp.coeFn_sub, Pi.sub_apply] using h
  rw [formENN, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hterm : ∀ n ∈ s, Tendsto (fun k => (formNN c (x k) n : ℝ≥0∞)) atTop
      (𝓝 (formNN c y n : ℝ≥0∞)) := by
    intro n _
    have h1 : Continuous fun z : ℂ => |c n| * ‖z‖ ^ 2 :=
      continuous_const.mul (continuous_norm.pow 2)
    have hg : Continuous fun z : ℂ => ENNReal.ofReal (|c n| * ‖z‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp h1
    have hlim : Tendsto (fun k => ENNReal.ofReal (|c n| * ‖(x k) n‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (|c n| * ‖y n‖ ^ 2))) :=
      hg.tendsto (y n) |> fun h => h.comp (hcoord n)
    simpa only [ENN_formNN] using hlim
  have hfin : Tendsto (fun k => ∑ n ∈ s, (formNN c (x k) n : ℝ≥0∞)) atTop
      (𝓝 (∑ n ∈ s, (formNN c y n : ℝ≥0∞))) :=
    tendsto_finset_sum s hterm
  exact le_of_tendsto hfin (Eventually.of_forall fun k =>
    (ENNReal.sum_le_tsum s).trans (hM k))

/-- **The form series of a nonnegative symbol, as `ofReal` of the real series.** -/
theorem formENN_eq_ofReal_formTsum {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) {x : L2 d}
    (hd : formDom c x) : formENN c x = ENNReal.ofReal (formTsum c x) := by
  have hsum : Summable fun n : Idx d => c n * ‖x n‖ ^ 2 := by
    simpa only [formDom, abs_of_nonneg (hc _)] using hd
  rw [formENN, formTsum]
  symm
  rw [ENNReal.ofReal_tsum_of_nonneg (f := fun n => c n * ‖x n‖ ^ 2)
    (fun n => mul_nonneg (hc n) (by positivity)) hsum]
  refine tsum_congr fun n => ?_
  rw [ENN_formNN, abs_of_nonneg (hc n)]

/-- **Closedness of the diagonal form**, in the real series: a bounded form-convergent sequence has
its limit in the form domain, and the form is lower semicontinuous there. -/
theorem formTsum_lsc {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) {x : ℕ → L2 d} {y : L2 d}
    (hx : Tendsto x atTop (𝓝 y)) (hdom : ∀ k, formDom c (x k)) {M : ℝ}
    (hM : ∀ k, formTsum c (x k) ≤ M) :
    formDom c y ∧ formTsum c y ≤ M := by
  have hENN : formENN c y ≤ ENNReal.ofReal M := by
    refine formENN_le_of_tendsto hx fun k => ?_
    rw [formENN_eq_ofReal_formTsum hc (hdom k)]
    exact ENNReal.ofReal_le_ofReal (hM k)
  have hdom' : formDom c y := formENN_ne_top_iff.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN)
  refine ⟨hdom', ?_⟩
  rw [formENN_eq_ofReal_formTsum hc hdom'] at hENN
  have hM0 : 0 ≤ formTsum c (x 0) := tsum_nonneg fun n => mul_nonneg (hc n) (sq_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff (hM0.trans (hM 0))).1 hENN

/-- **The sign-free form series as `ofReal` of the real series**, for an arbitrary symbol: the
quantity `formENN` of the form domain is `ofReal` of the sign-free real series. -/
theorem formENN_eq_ofReal_formTsumAbs {c : Idx d → ℝ} {x : L2 d} (hd : formDom c x) :
    formENN c x = ENNReal.ofReal (∑' n : Idx d, |c n| * ‖x n‖ ^ 2) := by
  rw [formENN]
  simp only [ENN_formNN]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun n => |c n| * ‖x n‖ ^ 2)
    (fun n => mul_nonneg (abs_nonneg (c n)) (sq_nonneg (‖x n‖))) hd]

/-- The form domain is closed: the limit of a form-bounded `L²`-convergent sequence stays in it. -/
theorem formDom_of_tendsto {c : Idx d → ℝ} {x : ℕ → L2 d} {y : L2 d}
    (hx : Tendsto x atTop (𝓝 y)) (hdom : ∀ k, formDom c (x k)) {M : ℝ}
    (hM : ∀ k, ∑' n : Idx d, |c n| * ‖(x k) n‖ ^ 2 ≤ M) : formDom c y := by
  have hENN : formENN c y ≤ ENNReal.ofReal M :=
    formENN_le_of_tendsto hx fun k => by
      rw [formENN_eq_ofReal_formTsumAbs (c := c) (x := x k) (hdom k)]
      exact ENNReal.ofReal_le_ofReal (hM k)
  exact formENN_ne_top_iff.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN)

/-- **KLMN, first inclusion**: a symbol relatively bounded by `c` with constants `a`, `β` has its
sum with `c` in the form domain wherever `c` is.  No condition on `a` is needed here. -/
theorem formDom_add_of_relativeBound {c b : Idx d → ℝ} {a β : ℝ}
    (hrel : ∀ n, |b n| ≤ a * |c n| + β) {x : L2 d} (hx : formDom c x) :
    formDom (fun n => c n + b n) x := by
  have hbound :
      Summable fun n : Idx d => (1 + a) * (|c n| * ‖x n‖ ^ 2) + β * ‖x n‖ ^ 2 :=
    (hx.mul_left (1 + a)).add (summable_normSq x |>.mul_left β)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbound
  have hu : (0 : ℝ) ≤ ‖x n‖ ^ 2 := sq_nonneg _
  have h1 : |c n + b n| ≤ |c n| + |b n| := abs_add_le _ _
  have h2 : |c n| + |b n| ≤ |c n| + (a * |c n| + β) := by linarith [hrel n]
  have h3 : (|c n| + (a * |c n| + β)) * ‖x n‖ ^ 2
      = (1 + a) * (|c n| * ‖x n‖ ^ 2) + β * ‖x n‖ ^ 2 := by ring
  calc |c n + b n| * ‖x n‖ ^ 2 ≤ (|c n| + |b n|) * ‖x n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hu
    _ ≤ (|c n| + (a * |c n| + β)) * ‖x n‖ ^ 2 := mul_le_mul_of_nonneg_right h2 hu
    _ = (1 + a) * (|c n| * ‖x n‖ ^ 2) + β * ‖x n‖ ^ 2 := h3

/-- **KLMN, second inclusion**: this is where the relative bound `a < 1` is used.  A state of the
perturbed form domain is a state of the unperturbed one, because `(1 − a)|c| ≤ |c + b| + β`
termwise. -/
theorem formDom_of_relativeBound_add {c b : Idx d → ℝ} {a β : ℝ} (ha1 : a < 1)
    (hrel : ∀ n, |b n| ≤ a * |c n| + β) {x : L2 d}
    (hx : formDom (fun n => c n + b n) x) : formDom c x := by
  have hpos : (0 : ℝ) < 1 - a := by linarith
  have hbound : Summable fun n : Idx d =>
      (1 - a)⁻¹ * (|c n + b n| * ‖x n‖ ^ 2) + (1 - a)⁻¹ * (β * ‖x n‖ ^ 2) :=
    (hx.mul_left (1 - a)⁻¹).add ((summable_normSq x |>.mul_left β).mul_left (1 - a)⁻¹)
  rw [formDom]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbound
  have hu : (0 : ℝ) ≤ ‖x n‖ ^ 2 := sq_nonneg _
  have hsplit : (c n + b n) + -(b n) = c n := by ring
  have h1 : |c n| ≤ |c n + b n| + |b n| := by
    simpa only [hsplit, abs_neg] using abs_add_le (c n + b n) (-(b n))
  have h2 : |c n + b n| + |b n| ≤ |c n + b n| + (a * |c n| + β) := by linarith [hrel n]
  have h3 : (1 - a) * |c n| ≤ |c n + b n| + β := by linarith
  have h4 : |c n| * ‖x n‖ ^ 2
      ≤ (1 - a)⁻¹ * ((|c n + b n| + β) * ‖x n‖ ^ 2) := by
    calc |c n| * ‖x n‖ ^ 2
        = (1 - a)⁻¹ * ((1 - a) * |c n|) * ‖x n‖ ^ 2 := by
          field_simp
      _ ≤ (1 - a)⁻¹ * (|c n + b n| + β) * ‖x n‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hu
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (1 - a)⁻¹ * ((|c n + b n| + β) * ‖x n‖ ^ 2) := by ring
  refine h4.trans (le_of_eq ?_)
  ring

/-- **KLMN lower bound on the form domain**: the sum form of a symbol bounded below by `θ` and a
perturbation with `|b n| ≤ a c n + β`, `a < 1`, is bounded below by `(1 − a)θ − β` on the *whole*
form domain.  §21's `formSum_ge` is the case `a = 0` on the operator domain. -/
theorem formSum_ge_formDom {c b : Idx d → ℝ} {a β θ : ℝ} (hc : ∀ n, 0 ≤ c n)
    (hθ : ∀ n, θ ≤ c n) (ha1 : a < 1) (hrel : ∀ n, |b n| ≤ a * c n + β)
    {x : L2 d} (hx : formDom c x) :
    ((1 - a) * θ - β) * ‖x‖ ^ 2 ≤ formTsum (fun n => c n + b n) x := by
  have hc' : formDom c x := hx
  have hdomB : formDom (fun n => c n + b n) x :=
    formDom_add_of_relativeBound (fun n => by
      rw [abs_of_nonneg (hc n)]
      exact hrel n) hx
  -- summabilities
  have hcS : Summable fun n : Idx d => c n * ‖x n‖ ^ 2 := by
    have h := hc'
    rw [formDom, show (fun n : Idx d => |c n| * ‖x n‖ ^ 2) = fun n => c n * ‖x n‖ ^ 2 from
      funext fun n => by rw [abs_of_nonneg (hc n)]] at h
    exact h
  have hBS : Summable fun n : Idx d => (c n + b n) * ‖x n‖ ^ 2 := by
    refine Summable.of_norm_bounded (g := fun n => |c n + b n| * ‖x n‖ ^ 2) hdomB ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (‖x n‖))]
  have hnorm : HasSum (fun n : Idx d => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa using h
  -- the comparison series
  have hleft : HasSum (fun n : Idx d => ((1 - a) * θ - β) * ‖x n‖ ^ 2)
      (((1 - a) * θ - β) * ‖x‖ ^ 2) := hnorm.mul_left _
  have hcmp : (∑' n : Idx d, ((1 - a) * θ - β) * ‖x n‖ ^ 2)
      ≤ ∑' n : Idx d, (c n + b n) * ‖x n‖ ^ 2 := by
    refine hleft.summable.tsum_le_tsum (fun n => ?_) hBS
    have hu : (0 : ℝ) ≤ ‖x n‖ ^ 2 := sq_nonneg _
    have hb : -(a * c n + β) ≤ b n := (abs_le.1 (hrel n)).1
    have h1 : (1 - a) * θ - β ≤ (1 - a) * c n - β := by
      have := mul_le_mul_of_nonneg_left (hθ n) (by linarith : (0 : ℝ) ≤ 1 - a)
      linarith
    have h2 : (1 - a) * c n - β ≤ c n + b n := by linarith
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hu
  have hfin := hcmp
  rwa [hleft.tsum_eq] at hfin

/-- **The KLMN operator is self-adjoint**: `diagUnb (c + b)` on the maximal domain, by §20. -/
theorem klmn_selfAdjoint {c b : Idx d → ℝ} :
    IsSelfAdjointOn (diagSub (fun n => c n + b n)) (diagSubLin (fun n => c n + b n)) :=
  diagSubLin_isSelfAdjointOn (fun n => c n + b n)

/-- **The KLMN operator's quadratic form is the sum form** — §21's form identity with the symbol
written out. -/
theorem klmn_form_eq_inner {c b : Idx d → ℝ} {x : L2 d}
    (hx : memDom (fun n => c n + b n) x) :
    (inner ℂ x (diagUnb (fun n => c n + b n) x hx)).re = formTsum (fun n => c n + b n) x :=
  (formTsum_eq_re_inner_diagUnb hx).symm

/-- **The KLMN operator's domain sits in the unperturbed form domain**: this is the inclusion that
makes `q_c` the form of the sum operator rather than an unrelated comparison form. -/
theorem klmn_formDom_of_operatorDomain {c b : Idx d → ℝ} {a β : ℝ} (ha1 : a < 1)
    (hrel : ∀ n, |b n| ≤ a * |c n| + β) {x : L2 d}
    (hx : memDom (fun n => c n + b n) x) : formDom c x :=
  formDom_of_relativeBound_add ha1 hrel (memDom_subset_formDom hx)

/-- **Kato–Rellich–KLMN for diagonal forms, in one statement.**  Let `c ≥ 0` be bounded below by
`θ`, and let `b` be relatively form bounded with `|b n| ≤ a c n + β` and `a < 1`.  Then the sum
symbol `c + b` is nonnegative, `diagUnb (c + b)` is self-adjoint on its maximal domain, its
quadratic form is the sum form, the sum form's domain is the unperturbed one, and the sum form is
bounded below by `(1 − a)θ − β` there. -/
theorem klmn {c b : Idx d → ℝ} {a β θ : ℝ} (hc : ∀ n, 0 ≤ c n) (hθ : ∀ n, θ ≤ c n)
    (ha1 : a < 1) (hrel : ∀ n, |b n| ≤ a * c n + β) :
    IsSelfAdjointOn (diagSub (fun n => c n + b n)) (diagSubLin (fun n => c n + b n)) ∧
      (∀ x : L2 d, formDom (fun n => c n + b n) x ↔ formDom c x) ∧
      (∀ x : L2 d, formDom c x →
        ((1 - a) * θ - β) * ‖x‖ ^ 2 ≤ formTsum (fun n => c n + b n) x) ∧
      (∀ (x : L2 d) (hx : memDom (fun n => c n + b n) x),
        (inner ℂ x (diagUnb (fun n => c n + b n) x hx)).re
          = formTsum (fun n => c n + b n) x) :=
  have hrel' : ∀ n, |b n| ≤ a * |c n| + β := fun n => by
    rw [abs_of_nonneg (hc n)]
    exact hrel n
  ⟨klmn_selfAdjoint,
   fun x => ⟨fun hx => formDom_of_relativeBound_add ha1 hrel' hx,
     fun hx => formDom_add_of_relativeBound hrel' hx⟩,
   fun x hx => formSum_ge_formDom hc hθ ha1 hrel hx,
   fun x hx => klmn_form_eq_inner hx⟩

/-! ## 24. The reduced sector's magnetic slot

§22 identifies the one-particle operator with the diagonal `T` of the form of record, and its
caveat says that the *reduced* sector's magnetic slot is not shown to be that diagonal form.  In the
coefficient model the two are the same object, and this section proves it:

* `reducedSector` — the **transverse sector**: states supported on the multi-indices with no
  occupation in the Cartan directions `T` (`parallelDegree T n = 0`).  This is the sector the BRST
  elimination of `softmodes.md` Phase 1 restricts to;
* **`diagUnb_mem_reducedSector`** — the diagonal operator *preserves* the sector, coordinate by
  coordinate.  This is the statement that the reduction cannot introduce an off-diagonal magnetic
  ladder: every matrix element between sector states and non-sector states is zero, because the
  operator never mixes multi-indices;
* **`yangMillsSymbol_on_sector`** — on the sector the barrier term is the constant
  `rootCount T · zeroPoint g 0`, so the symbol there is `N + N² + B` with `B` the vacuum energy:
  the barrier does not depend on the state once the Cartan occupation is zero;
* **`sector_gap`** — consequently the sector form has the same gap `2` above the vacuum: restricting
  to the transverse sector cannot lower the bottom, at the level of §22's symbol rather than of a
  separate comparison estimate;
* **`sector_gap_pos`** — the rate is strictly positive for every `g ≥ 0`, which is the form the mass
  gap takes in the coefficient model.

What this does **not** claim: the identification of the transversal sector with the BRST quotient
`H/(exact ⊕ harmonic)` — that needs `closure (range Ω) = span{∂_i φ}` (`ChapterBrstReducedTransfer`,
open item 3 of Phase 1) — and therefore nothing here is a statement about the physical continuum
Hamiltonian.  What is removed is the model-level objection: within the diagonal model the reduced
sector's magnetic slot *is* the diagonal `:N²:` slot, and an off-diagonal ladder cannot appear by
restriction.
-/

section ReducedSector

open BookProof.YangMillsEffectiveBarrier

variable {T : Finset (Fin d)} {g : ℝ}

/-- The **transverse (reduced) sector of the coefficient model**: states whose coefficients vanish
on every multi-index with a nonzero Cartan occupation. -/
def reducedSector (T : Finset (Fin d)) : Submodule ℂ (L2 d) where
  carrier := {x | ∀ n : Idx d, parallelDegree T n ≠ 0 → x n = 0}
  zero_mem' := by
    intro n _
    simp
  add_mem' := by
    intro x y hx hy n hn
    rw [lp.coeFn_add, Pi.add_apply, hx n hn, hy n hn, add_zero]
  smul_mem' := by
    intro a x hx n hn
    rw [lp.coeFn_smul, Pi.smul_apply, hx n hn, smul_zero]

/-- **The diagonal operator preserves the reduced sector** — no coordinate mixing, so the
restriction of §22's operator to the sector is again a diagonal operator, and the sector's magnetic
slot is the diagonal one rather than an off-diagonal ladder. -/
theorem diagUnb_mem_reducedSector {c : Idx d → ℝ} {x : L2 d} (hx : x ∈ reducedSector T)
    (hm : memDom c x) : diagUnb c x hm ∈ reducedSector T := by
  intro n hn
  rw [diagUnb_apply, hx n hn, mul_zero]

/-- **On the sector the barrier is the vacuum barrier**: the Cartan occupation is zero, so the
zero-point term does not depend on the state. -/
theorem barrier_on_sector {n : Idx d} (hn : parallelDegree T n = 0) :
    rootCount T * zeroPoint g (parallelDegree T n) = rootCount T * zeroPoint g 0 :=
  congrArg (fun N => rootCount T * zeroPoint g N) hn

/-- **The symbol on the reduced sector**: kinetic occupancy, its square (the magnetic `:N²:` slot)
and the constant vacuum barrier.  This is the identification of the sector's magnetic slot with the
diagonal one of §22. -/
theorem yangMillsSymbol_on_sector {n : Idx d} (hn : parallelDegree T n = 0) :
    yangMillsSymbol T g n
      = (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2 + rootCount T * zeroPoint g 0 := by
  rw [yangMillsSymbol, barrier_on_sector hn]

/-- **The gap survives the reduction.**  On the transverse sector and off the vacuum, the form of
§22 is bounded below by the vacuum energy plus `2`: the sector restriction removes the eliminated
directions but not the gap, because the symbol is read coordinate by coordinate. -/
theorem sector_gap {g : ℝ} (hg : 0 ≤ g) (x : reducedSector T)
    (hdom : formDom (yangMillsSymbol T g) (x : L2 d)) (hvac : (x : L2 d) 0 = 0) :
    (rootCount T * zeroPoint g 0 + 2) * ‖(x : L2 d)‖ ^ 2
      ≤ ∑' n : Idx d, yangMillsSymbol T g n * ‖(x : L2 d) n‖ ^ 2 := by
  have hterm : ∀ n : Idx d, (rootCount T * zeroPoint g 0 + 2) * ‖(x : L2 d) n‖ ^ 2
      ≤ yangMillsSymbol T g n * ‖(x : L2 d) n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [hvac]
      simp
    · exact mul_le_mul_of_nonneg_right (yangMillsSymbol_ge hg hn) (sq_nonneg _)
  have hnorm : HasSum (fun n : Idx d => ‖(x : L2 d) n‖ ^ 2) (‖(x : L2 d)‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num)
      (x : L2 d)
    simpa using h
  have hleft : HasSum (fun n : Idx d => (rootCount T * zeroPoint g 0 + 2) * ‖(x : L2 d) n‖ ^ 2)
      ((rootCount T * zeroPoint g 0 + 2) * ‖(x : L2 d)‖ ^ 2) := hnorm.mul_left _
  have hright : Summable fun n : Idx d =>
      yangMillsSymbol T g n * ‖(x : L2 d) n‖ ^ 2 := by
    refine Summable.of_norm_bounded
      (g := fun n => |yangMillsSymbol T g n| * ‖(x : L2 d) n‖ ^ 2) hdom ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (‖(x : L2 d) n‖))]
  have hcmp : (∑' n : Idx d, (rootCount T * zeroPoint g 0 + 2) * ‖(x : L2 d) n‖ ^ 2)
      ≤ ∑' n : Idx d, yangMillsSymbol T g n * ‖(x : L2 d) n‖ ^ 2 :=
    hleft.summable.tsum_le_tsum hterm hright
  rwa [hleft.tsum_eq] at hcmp

/-- **The reduced sector's gap is positive**: `2` above a vacuum energy that is itself
nonnegative, for every `g ≥ 0`. -/
theorem sector_gap_pos {g : ℝ} (hg : 0 ≤ g) : 0 < rootCount T * zeroPoint g 0 + 2 := by
  have h1 : 0 ≤ rootCount T * zeroPoint g 0 :=
    mul_nonneg (rootCount_nonneg T) (zeroPoint_nonneg hg (le_refl (0 : ℝ)))
  linarith

end ReducedSector

end BookProof.YangMillsFormClosureND
