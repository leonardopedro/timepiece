module

public import BayesianTransformer.Transformer.LipschitzCalculus
public import BayesianTransformer.Transformer.CosineAttention
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The per-example gradient bound, derived from the nGPT architecture

`GlobalLipschitz.lean` *assumes* (field `NGPTModel.uniform_grad_bound`) that every per-example
loss has a uniformly bounded derivative. Here we define a concrete normalized transformer
(nGPT-style) and *derive* that bound from its architecture.

## The architecture

* Hidden dimension: a real inner product space `E`; sequence positions: a finite type `ι`;
  vocabulary: a finite type `V`; depth `L`.
* Parameters (`NGPTParams E V L`): for each layer six weight matrices
  `W_q, W_k, W_v, W_o, W_up, W_down : E →L[ℝ] E`, and one output (unembedding) vector `u_v ∈ E`
  per vocabulary item. Every weight is used only through its normalization `Ŵ = W / ‖W‖`
  (`normalizeVec`, operator norm for matrices), as in nGPT.
* Hyperparameters (`NGPTConfig E`): attention logit scale `s_qk`, output logit scale `s_z`,
  eigen learning rates `α_A, α_M ∈ [0, 1/2)`, and an activation `σ : E → E` that is
  `1`-Lipschitz with `σ 0 = 0` (e.g. a coordinatewise ReLU).
* One layer on a sequence of unit vectors `h : ι → E`:
  - attention logits `z_ij = s_qk ⟪Ŵ_q h_i, Ŵ_k h_j⟫`, weights `p_i = softmax z_i`,
    output `a_i = Ŵ_o (∑_j p_ij Ŵ_v h_j)`;
  - `h'_i = Norm(h_i + α_A (a_i - h_i))`;
  - MLP `m_i = Ŵ_down σ(Ŵ_up h'_i)`, and `h''_i = Norm(h'_i + α_M (m_i - h'_i))`.
* Output: logits `z_iv = s_z ⟪û_v, h^L_i⟫` (cosine logits) and the loss of an example
  `(x, y)` (`x : ι → E` unit input embeddings, `y : ι → V` targets) is the average over positions
  of the cross entropy `log ∑_v exp z_iv - z_{i y_i}` (`exampleLoss`).

## Results

On the parameter domain `paramDomain ε` (every weight has norm `≥ ε > 0`):

* `ngpt_exampleLoss_lipschitzOn`: there is `M`, depending only on the hyperparameters, `ε`, the
  depth and the sequence length, such that every per-example loss is `M`-Lipschitz in the
  parameters, uniformly over all examples.
* `ngpt_exampleLoss_fderiv_bound`: consequently `‖∇_θ ℓ(θ; x, y)‖ ≤ M` for every `θ` in the
  domain and every example (this is the per-example bound assumed in `NGPTModel`).
* `ngpt_empiricalRisk_fderiv_bound`: the same ceiling for the empirical risk over any dataset.

## Modelling choices (deviations from the nGPT paper)

* Matrices are normalized by their operator norm (spectral normalization) rather than row by row.
* Queries/keys and sublayer outputs are not re-normalized: their boundedness (`‖·‖ ≤ 1`), which
  is what the normalization serves for, already follows from the normalized weights. Normalizing
  a vector that may vanish is not Lipschitz, so this is needed for a uniform bound.
* `s_qk`, `s_z`, `α_A`, `α_M` are fixed hyperparameters (if they were trainable and unbounded no
  uniform bound could hold), and `α < 1/2` guarantees that the hidden-state normalizations are
  applied to vectors of norm `≥ 1 - 2α > 0`.
* The input embeddings are part of the example (unit vectors), not trained parameters.
* The bound holds on `{‖W‖ ≥ ε}` only: because the loss is invariant under rescaling each weight,
  its gradient scales like `1/‖W‖`, so no bound can hold uniformly as `‖W‖ → 0`.
-/

@[expose] public section

open Filter Topology

namespace BayesianTransformer

/-- The six weight matrices of an nGPT layer. -/
inductive WeightKind
  | query | key | value | out | up | down
  deriving Fintype, DecidableEq

/-- Parameters of an `L`-layer nGPT: six matrices per layer and one unembedding vector per
vocabulary item. -/
abbrev NGPTParams (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : Type*)
    (L : ℕ) :=
  (Fin L → WeightKind → (E →L[ℝ] E)) × (V → E)

/-- Fixed hyperparameters of the network. -/
structure NGPTConfig (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- attention logit scale -/
  sQK : ℝ
  /-- output logit scale -/
  sZ : ℝ
  /-- eigen learning rate of the attention update -/
  alphaA : ℝ
  /-- eigen learning rate of the MLP update -/
  alphaM : ℝ
  alphaA_nonneg : 0 ≤ alphaA
  alphaA_lt : alphaA < 1 / 2
  alphaM_nonneg : 0 ≤ alphaM
  alphaM_lt : alphaM < 1 / 2
  /-- the MLP activation -/
  act : E → E
  act_lipschitz : LipschitzWith 1 act
  act_zero : act 0 = 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] {V : Type*} [Fintype V] {L : ℕ}

/-- Cosine-style attention logits of position `i`. -/
noncomputable def attnLogits (Wq Wk : E →L[ℝ] E) (s : ℝ) (h : ι → E) (i : ι) : ι → ℝ :=
  fun j => s * inner ℝ (Wq (h i)) (Wk (h j))

/-- Attention-weighted mixture of the values at position `i`. -/
noncomputable def attnMix (Wq Wk Wv : E →L[ℝ] E) (s : ℝ) (h : ι → E) (i : ι) : E :=
  ∑ j, softmax (attnLogits Wq Wk s h i) j • Wv (h j)

/-- Attention output at position `i`. -/
noncomputable def attnOut (Wq Wk Wv Wo : E →L[ℝ] E) (s : ℝ) (h : ι → E) (i : ι) : E :=
  Wo (attnMix Wq Wk Wv s h i)

/-- nGPT residual update followed by renormalization: `Norm(h + α (a - h))`. -/
noncomputable def residualNorm (α : ℝ) (h a : E) : E := normalizeVec (h + α • (a - h))

/-- The MLP block. -/
noncomputable def mlpOut (act : E → E) (Wup Wdown : E →L[ℝ] E) (x : E) : E := Wdown (act (Wup x))

/-- One nGPT layer (attention update, then MLP update), all weights normalized. -/
noncomputable def ngptLayer (cfg : NGPTConfig E) (W : WeightKind → (E →L[ℝ] E)) (h : ι → E) :
    ι → E :=
  let Wn := fun k => normalizeVec (W k)
  let h' := fun i => residualNorm cfg.alphaA (h i)
    (attnOut (Wn .query) (Wn .key) (Wn .value) (Wn .out) cfg.sQK h i)
  fun i => residualNorm cfg.alphaM (h' i) (mlpOut cfg.act (Wn .up) (Wn .down) (h' i))

/-- Hidden states after `k` layers (layers beyond `L` act as the identity). -/
noncomputable def hiddenStates (cfg : NGPTConfig E) (θ : NGPTParams E V L) (x : ι → E) :
    ℕ → ι → E
  | 0 => x
  | k + 1 => if hk : k < L then ngptLayer cfg (θ.1 ⟨k, hk⟩) (hiddenStates cfg θ x k)
      else hiddenStates cfg θ x k

/-- Cosine output logits at position `i`. -/
noncomputable def outputLogits (cfg : NGPTConfig E) (θ : NGPTParams E V L) (x : ι → E) (i : ι) :
    V → ℝ :=
  fun v => cfg.sZ * inner ℝ (normalizeVec (θ.2 v)) (hiddenStates cfg θ x L i)

/-- Cross-entropy loss of logits `z` against the target `y`. -/
noncomputable def crossEntropy (z : V → ℝ) (y : V) : ℝ := Real.log (expSum z) - z y

/-- Per-example loss: average cross entropy over the positions of the sequence. -/
noncomputable def exampleLoss (cfg : NGPTConfig E) (θ : NGPTParams E V L) (x : ι → E)
    (y : ι → V) : ℝ :=
  (∑ i, crossEntropy (outputLogits cfg θ x i) (y i)) / (Fintype.card ι : ℝ)

/-- The parameter domain on which every weight has norm at least `ε`. -/
def paramDomain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : Type*) (L : ℕ)
    (ε : ℝ) : Set (NGPTParams E V L) :=
  {θ | (∀ l k, ε ≤ ‖θ.1 l k‖) ∧ ∀ v, ε ≤ ‖θ.2 v‖}

/-! ### Norm bounds along the forward pass -/

theorem softmax_le_one (z : ι → ℝ) (j : ι) : softmax z j ≤ 1 := by
  haveI : Nonempty ι := ⟨j⟩
  rw [softmax_apply, mul_inv_le_iff₀ (expSum_pos z), one_mul]
  exact exp_le_expSum z j

theorem abs_softmax_le_one (z : ι → ℝ) (j : ι) : |softmax z j| ≤ 1 := by
  rw [abs_of_pos (softmax_pos z j)]; exact softmax_le_one z j

theorem norm_clm_apply_le_one {W : E →L[ℝ] E} {v : E} (hW : ‖W‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖W v‖ ≤ 1 :=
  (W.le_opNorm v).trans (by nlinarith [norm_nonneg W, norm_nonneg v])

theorem norm_attnMix_le {Wq Wk Wv : E →L[ℝ] E} (hv : ‖Wv‖ ≤ 1) (s : ℝ)
    {h : ι → E} (hh : ∀ j, ‖h j‖ ≤ 1) (i : ι) : ‖attnMix Wq Wk Wv s h i‖ ≤ 1 := by
  haveI : Nonempty ι := ⟨i⟩
  calc ‖∑ j, softmax (attnLogits Wq Wk s h i) j • Wv (h j)‖
      ≤ ∑ j, ‖softmax (attnLogits Wq Wk s h i) j • Wv (h j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, softmax (attnLogits Wq Wk s h i) j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (softmax_pos _ _)]
        exact mul_le_of_le_one_right (softmax_pos _ _).le (norm_clm_apply_le_one hv (hh j))
    _ = 1 := softmax_sum_eq_one _

theorem norm_attnOut_le {Wq Wk Wv Wo : E →L[ℝ] E} (hv : ‖Wv‖ ≤ 1) (ho : ‖Wo‖ ≤ 1) (s : ℝ)
    {h : ι → E} (hh : ∀ j, ‖h j‖ ≤ 1) (i : ι) : ‖attnOut Wq Wk Wv Wo s h i‖ ≤ 1 :=
  norm_clm_apply_le_one ho (norm_attnMix_le hv s hh i)

theorem norm_act_le (cfg : NGPTConfig E) (v : E) : ‖cfg.act v‖ ≤ ‖v‖ := by
  have := cfg.act_lipschitz.dist_le_mul v 0
  simpa [cfg.act_zero] using this

theorem norm_mlpOut_le (cfg : NGPTConfig E) {Wup Wdown : E →L[ℝ] E} (hu : ‖Wup‖ ≤ 1)
    (hd : ‖Wdown‖ ≤ 1) {v : E} (hv : ‖v‖ ≤ 1) : ‖mlpOut cfg.act Wup Wdown v‖ ≤ 1 :=
  norm_clm_apply_le_one hd ((norm_act_le cfg _).trans (norm_clm_apply_le_one hu hv))

/-- The vector renormalized by an nGPT update has norm at least `1 - 2α > 0`. -/
theorem residual_norm_ge {α : ℝ} (hα : 0 ≤ α) {h a : E} (hh : ‖h‖ = 1) (ha : ‖a‖ ≤ 1) :
    1 - 2 * α ≤ ‖h + α • (a - h)‖ := by
  have h1 : ‖α • (a - h)‖ ≤ 2 * α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
    have : ‖a - h‖ ≤ 2 := (norm_sub_le a h).trans (by linarith)
    nlinarith
  have h2 := norm_sub_norm_le h (-(α • (a - h)))
  rw [sub_neg_eq_add, norm_neg] at h2
  linarith

theorem norm_residualNorm {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 1 / 2) {h a : E} (hh : ‖h‖ = 1)
    (ha : ‖a‖ ≤ 1) : ‖residualNorm α h a‖ = 1 := by
  refine norm_normalizeVec ?_
  intro h0
  have := residual_norm_ge hα hh ha
  rw [h0, norm_zero] at this
  linarith

theorem norm_ngptLayer (cfg : NGPTConfig E) (W : WeightKind → (E →L[ℝ] E)) {h : ι → E}
    (hh : ∀ i, ‖h i‖ = 1) (i : ι) : ‖ngptLayer cfg W h i‖ = 1 := by
  have hW : ∀ k, ‖normalizeVec (W k)‖ ≤ 1 := fun k => norm_normalizeVec_le _
  have h' : ‖residualNorm cfg.alphaA (h i) (attnOut (normalizeVec (W .query))
      (normalizeVec (W .key)) (normalizeVec (W .value)) (normalizeVec (W .out)) cfg.sQK h i)‖
      = 1 :=
    norm_residualNorm cfg.alphaA_nonneg cfg.alphaA_lt (hh i)
      (norm_attnOut_le (hW _) (hW _) _ (fun j => (hh j).le) i)
  exact norm_residualNorm cfg.alphaM_nonneg cfg.alphaM_lt h'
    (norm_mlpOut_le cfg (hW _) (hW _) h'.le)

omit [Fintype V] in
theorem norm_hiddenStates (cfg : NGPTConfig E) (θ : NGPTParams E V L) {x : ι → E}
    (hx : ∀ i, ‖x i‖ = 1) (k : ℕ) (i : ι) : ‖hiddenStates cfg θ x k i‖ = 1 := by
  induction k generalizing i with
  | zero => exact hx i
  | succ k ih =>
    simp only [hiddenStates]
    split_ifs
    · exact norm_ngptLayer cfg _ ih i
    · exact ih i


/-! ### Lipschitz constants of the blocks, as functions of the parameters -/

section Blocks

variable {P : Type*} [PseudoMetricSpace P] {D : Set P}

/-- Lipschitz constant of the attention block. -/
noncomputable def attnConst (Kw Kh s : ℝ) (n : ℕ) : ℝ :=
  Kw + n * (2 * (|s| * (2 * (Kw + Kh))) + (Kw + Kh))

theorem attnConst_nonneg {Kw Kh : ℝ} (hKw : 0 ≤ Kw) (hKh : 0 ≤ Kh) (s : ℝ) (n : ℕ) :
    0 ≤ attnConst Kw Kh s n := by
  unfold attnConst; positivity

theorem lipOn_clm_apply_vec {W : P → E →L[ℝ] E} {H : P → ι → E} {Kw Kh : ℝ} (hKw : 0 ≤ Kw)
    (hW : LipOn W D Kw) (nW : ∀ a, ‖W a‖ ≤ 1) (hH : LipOn H D Kh) (nH : ∀ a j, ‖H a j‖ ≤ 1)
    (j : ι) : LipOn (fun a => W a (H a j)) D (Kw + Kh) :=
  (hW.clm_apply (hH.apply j) (fun a _ => nW a) (fun a _ => nH a j) hKw).mono
    (le_of_eq (by ring))

theorem lipOn_attnOut {Wq Wk Wv Wo : P → E →L[ℝ] E} {H : P → ι → E} {Kw Kh : ℝ}
    (hKw : 0 ≤ Kw) (hKh : 0 ≤ Kh)
    (hq : LipOn Wq D Kw) (hk : LipOn Wk D Kw) (hv : LipOn Wv D Kw) (ho : LipOn Wo D Kw)
    (nq : ∀ a, ‖Wq a‖ ≤ 1) (nk : ∀ a, ‖Wk a‖ ≤ 1) (nv : ∀ a, ‖Wv a‖ ≤ 1)
    (no : ∀ a, ‖Wo a‖ ≤ 1)
    (hH : LipOn H D Kh) (nH : ∀ a j, ‖H a j‖ ≤ 1) (s : ℝ) (i : ι) :
    LipOn (fun a => attnOut (Wq a) (Wk a) (Wv a) (Wo a) s (H a) i) D
      (attnConst Kw Kh s (Fintype.card ι)) := by
  have hlogit : LipOn (fun a => attnLogits (Wq a) (Wk a) s (H a) i) D
      (|s| * (2 * (Kw + Kh))) := by
    refine LipOn.pi (by positivity) fun j => ?_
    have h1 := lipOn_clm_apply_vec hKw hq nq hH nH i
    have h2 := lipOn_clm_apply_vec hKw hk nk hH nH j
    have h3 := (h1.real_inner h2 (Bf := 1) (Bg := 1)
      (fun a _ => norm_clm_apply_le_one (nq a) (nH a i))
      (fun a _ => norm_clm_apply_le_one (nk a) (nH a j)) (by positivity)).const_smul s
    exact h3.mono (le_of_eq (by ring))
  have hp : LipOn (fun a => softmax (attnLogits (Wq a) (Wk a) s (H a) i)) D
      (2 * (|s| * (2 * (Kw + Kh)))) :=
    hlogit.comp (g := fun z : ι → ℝ => softmax z) (by norm_num)
      (fun y y' => by simpa using softmax_lipschitzWith_two.dist_le_mul y y')
  have hterm : ∀ j ∈ (Finset.univ : Finset ι),
      LipOn (fun a => softmax (attnLogits (Wq a) (Wk a) s (H a) i) j • Wv a (H a j)) D
        (2 * (|s| * (2 * (Kw + Kh))) + (Kw + Kh)) := fun j _ => by
    have h1 : LipOn (fun a => softmax (attnLogits (Wq a) (Wk a) s (H a) i) j) D
        (2 * (|s| * (2 * (Kw + Kh)))) := hp.apply j
    have h2 := lipOn_clm_apply_vec hKw hv nv hH nH j
    have h3 := h1.smul h2 (Bp := 1) (Bg := 1) (fun a _ => abs_softmax_le_one _ _)
      (fun a _ => norm_clm_apply_le_one (nv a) (nH a j)) (by positivity)
    exact h3.mono (le_of_eq (by ring))
  have hmix : LipOn (fun a => attnMix (Wq a) (Wk a) (Wv a) s (H a) i) D
      (Fintype.card ι * (2 * (|s| * (2 * (Kw + Kh))) + (Kw + Kh))) := by
    have := LipOn.sum Finset.univ hterm
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  exact (ho.clm_apply hmix (fun a _ => no a) (fun a _ => norm_attnMix_le (nv a) s (nH a) i)
    hKw).mono (le_of_eq (by unfold attnConst; ring))

theorem lipOn_residualNorm {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 1 / 2) {h a : P → E} {Kh Ka : ℝ}
    (hh : LipOn h D Kh) (ha : LipOn a D Ka) (nh : ∀ p, ‖h p‖ = 1) (na : ∀ p, ‖a p‖ ≤ 1) :
    LipOn (fun p => residualNorm α (h p) (a p)) D (2 / (1 - 2 * α) * (Kh + α * (Ka + Kh))) := by
  have hin := hh.add ((ha.sub hh).const_smul α)
  rw [abs_of_nonneg hα] at hin
  have hpos : 0 < 1 - 2 * α := by linarith
  exact hin.comp_on (S := {v | 1 - 2 * α ≤ ‖v‖}) (div_nonneg zero_le_two hpos.le)
    (fun y hy y' hy' => dist_normalizeVec_le hpos hy hy')
    (fun p _ => residual_norm_ge hα (nh p) (na p))

theorem lipOn_mlpOut (cfg : NGPTConfig E) {Wu Wd : P → E →L[ℝ] E} {H : P → E} {Kw Kh : ℝ}
    (hKw : 0 ≤ Kw) (hu : LipOn Wu D Kw) (hd : LipOn Wd D Kw) (nu : ∀ a, ‖Wu a‖ ≤ 1)
    (nd : ∀ a, ‖Wd a‖ ≤ 1) (hH : LipOn H D Kh) (nH : ∀ a, ‖H a‖ ≤ 1) :
    LipOn (fun a => mlpOut cfg.act (Wu a) (Wd a) (H a)) D (Kw + (Kw + Kh)) := by
  have h1 := hu.clm_apply hH (fun a _ => nu a) (fun a _ => nH a) hKw
  have h2 := h1.comp (g := cfg.act) zero_le_one
    (fun y y' => by simpa using cfg.act_lipschitz.dist_le_mul y y')
  have h3 := hd.clm_apply h2 (fun a _ => nd a)
    (fun a _ => (norm_act_le cfg _).trans (norm_clm_apply_le_one (nu a) (nH a))) hKw
  exact h3.mono (le_of_eq (by ring))

/-- Lipschitz constant of one nGPT layer, given the constant `Kw` of the normalized weights and
the constant `Kh` of the incoming hidden states. -/
noncomputable def layerConst (cfg : NGPTConfig E) (Kw Kh : ℝ) (n : ℕ) : ℝ :=
  2 / (1 - 2 * cfg.alphaM) *
    (2 / (1 - 2 * cfg.alphaA) * (Kh + cfg.alphaA * (attnConst Kw Kh cfg.sQK n + Kh)) +
      cfg.alphaM * ((Kw + (Kw + 2 / (1 - 2 * cfg.alphaA) *
        (Kh + cfg.alphaA * (attnConst Kw Kh cfg.sQK n + Kh)))) +
        2 / (1 - 2 * cfg.alphaA) * (Kh + cfg.alphaA * (attnConst Kw Kh cfg.sQK n + Kh))))

theorem layerConst_nonneg (cfg : NGPTConfig E) {Kw Kh : ℝ} (hKw : 0 ≤ Kw) (hKh : 0 ≤ Kh)
    (n : ℕ) : 0 ≤ layerConst cfg Kw Kh n := by
  have hA : 0 ≤ 2 / (1 - 2 * cfg.alphaA) := div_nonneg zero_le_two (by linarith [cfg.alphaA_lt])
  have hM : 0 ≤ 2 / (1 - 2 * cfg.alphaM) := div_nonneg zero_le_two (by linarith [cfg.alphaM_lt])
  have := attnConst_nonneg hKw hKh cfg.sQK n
  have := cfg.alphaA_nonneg
  have := cfg.alphaM_nonneg
  unfold layerConst
  positivity

theorem lipOn_ngptLayer (cfg : NGPTConfig E) {W : P → WeightKind → (E →L[ℝ] E)}
    {H : P → ι → E} {Kw Kh : ℝ} (hKw : 0 ≤ Kw) (hKh : 0 ≤ Kh)
    (hW : ∀ k, LipOn (fun p => normalizeVec (W p k)) D Kw) (hH : LipOn H D Kh)
    (nH : ∀ p i, ‖H p i‖ = 1) :
    LipOn (fun p => ngptLayer cfg (W p) (H p)) D (layerConst cfg Kw Kh (Fintype.card ι)) := by
  refine LipOn.pi (layerConst_nonneg cfg hKw hKh _) fun i => ?_
  have nW : ∀ k p, ‖normalizeVec (W p k)‖ ≤ 1 := fun k p => norm_normalizeVec_le _
  have hA := lipOn_attnOut hKw hKh (hW .query) (hW .key) (hW .value) (hW .out) (nW _) (nW _)
    (nW _) (nW _) hH (fun p j => (nH p j).le) cfg.sQK i
  have h1 := lipOn_residualNorm cfg.alphaA_nonneg cfg.alphaA_lt (hH.apply i) hA (fun p => nH p i)
    (fun p => norm_attnOut_le (nW .value p) (nW .out p) _ (fun j => (nH p j).le) i)
  have n1 : ∀ p, ‖residualNorm cfg.alphaA (H p i) (attnOut (normalizeVec (W p .query))
      (normalizeVec (W p .key)) (normalizeVec (W p .value)) (normalizeVec (W p .out))
      cfg.sQK (H p) i)‖ = 1 := fun p =>
    norm_residualNorm cfg.alphaA_nonneg cfg.alphaA_lt (nH p i)
      (norm_attnOut_le (nW .value p) (nW .out p) _ (fun j => (nH p j).le) i)
  have h2 := lipOn_mlpOut cfg hKw (hW .up) (hW .down) (nW .up) (nW .down) h1 (fun p => (n1 p).le)
  exact lipOn_residualNorm cfg.alphaM_nonneg cfg.alphaM_lt h1 h2 n1
    (fun p => norm_mlpOut_le cfg (nW .up p) (nW .down p) (n1 p).le)

end Blocks

/-! ### The whole network on the parameter domain -/

section Network

theorem dist_crossEntropy_le (z z' : V → ℝ) (y : V) :
    dist (crossEntropy z y) (crossEntropy z' y) ≤ 2 * dist z z' := by
  haveI : Nonempty V := ⟨y⟩
  have hlse : ∀ w w' : V → ℝ, Real.log (expSum w) ≤ Real.log (expSum w') + dist w w' := by
    intro w w'
    have hle : expSum w ≤ Real.exp (dist w w') * expSum w' := by
      rw [expSum, expSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      have := (Real.dist_eq _ _ ▸ dist_le_pi_dist w w' j : |w j - w' j| ≤ dist w w')
      linarith [(abs_le.mp this).2]
    have := Real.log_le_log (expSum_pos w) hle
    rw [Real.log_mul (Real.exp_pos _).ne' (expSum_pos w').ne', Real.log_exp] at this
    linarith
  have hy : |z y - z' y| ≤ dist z z' := Real.dist_eq _ _ ▸ dist_le_pi_dist z z' y
  have h1 := hlse z z'
  have h2 := hlse z' z
  rw [dist_comm z' z] at h2
  rw [Real.dist_eq, crossEntropy, crossEntropy, abs_le]
  constructor <;> linarith [(abs_le.mp hy).1, (abs_le.mp hy).2]

theorem lipOn_fst_apply (ε : ℝ) (l : Fin L) (k : WeightKind) :
    LipOn (fun θ : NGPTParams E V L => θ.1 l k) (paramDomain E V L ε) 1 := fun a _ b _ => by
  rw [one_mul]
  exact (dist_le_pi_dist (a.1 l) (b.1 l) k).trans
    ((dist_le_pi_dist a.1 b.1 l).trans (le_max_left _ _))

theorem lipOn_snd_apply (ε : ℝ) (v : V) :
    LipOn (fun θ : NGPTParams E V L => θ.2 v) (paramDomain E V L ε) 1 := fun a _ b _ => by
  rw [one_mul]
  exact (dist_le_pi_dist a.2 b.2 v).trans (le_max_right _ _)

theorem lipOn_normalized_weight {ε : ℝ} (hε : 0 < ε) (l : Fin L) (k : WeightKind) :
    LipOn (fun θ : NGPTParams E V L => normalizeVec (θ.1 l k)) (paramDomain E V L ε)
      (2 / ε) := by
  have := (lipOn_fst_apply (E := E) (V := V) ε l k).comp_on (S := {W | ε ≤ ‖W‖})
    (div_nonneg zero_le_two hε.le) (fun y hy y' hy' => dist_normalizeVec_le hε hy hy')
    (fun θ hθ => hθ.1 l k)
  simpa using this

theorem lipOn_normalized_unembed {ε : ℝ} (hε : 0 < ε) (v : V) :
    LipOn (fun θ : NGPTParams E V L => normalizeVec (θ.2 v)) (paramDomain E V L ε)
      (2 / ε) := by
  have := (lipOn_snd_apply (E := E) (L := L) ε v).comp_on (S := {W | ε ≤ ‖W‖})
    (div_nonneg zero_le_two hε.le) (fun y hy y' hy' => dist_normalizeVec_le hε hy hy')
    (fun θ hθ => hθ.2 v)
  simpa using this

/-- The hidden states after `k` layers are Lipschitz in the parameters, with a constant that is
uniform over all inputs. -/
theorem lipOn_hiddenStates (cfg : NGPTConfig E) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ι → E, (∀ i, ‖x i‖ = 1) →
      LipOn (fun θ : NGPTParams E V L => hiddenStates cfg θ x k) (paramDomain E V L ε) K := by
  induction k with
  | zero => exact ⟨0, le_rfl, fun x _ => LipOn.const x⟩
  | succ k ih =>
    obtain ⟨K, hK, hlip⟩ := ih
    by_cases hk : k < L
    · refine ⟨layerConst cfg (2 / ε) K (Fintype.card ι),
        layerConst_nonneg cfg (div_nonneg zero_le_two hε.le) hK _, fun x hx => ?_⟩
      simp only [hiddenStates, dif_pos hk]
      exact lipOn_ngptLayer cfg (div_nonneg zero_le_two hε.le) hK
        (fun kind => lipOn_normalized_weight hε _ kind) (hlip x hx)
        (fun θ i => norm_hiddenStates cfg θ hx k i)
    · refine ⟨K, hK, fun x hx => ?_⟩
      simp only [hiddenStates, dif_neg hk]
      exact hlip x hx

/-- **Per-example Lipschitz bound derived from the architecture.** On the domain where every
weight has norm at least `ε`, there is a constant `M` (depending only on the hyperparameters,
`ε`, the depth and the sequence length) such that the loss of *every* example is `M`-Lipschitz
in the parameters. -/
theorem ngpt_exampleLoss_lipOn (cfg : NGPTConfig E) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ι → E, (∀ i, ‖x i‖ = 1) → ∀ y : ι → V,
      LipOn (fun θ : NGPTParams E V L => exampleLoss cfg θ x y) (paramDomain E V L ε) M := by
  obtain ⟨K, hK, hlip⟩ := lipOn_hiddenStates (V := V) (L := L) (ι := ι) cfg hε L
  set Kz := |cfg.sZ| * (2 / ε + K) with hKz
  have hKz0 : 0 ≤ Kz := by positivity
  refine ⟨|(Fintype.card ι : ℝ)⁻¹| * ∑ _i : ι, 2 * Kz, by positivity, fun x hx y => ?_⟩
  have hz : ∀ i, LipOn (fun θ : NGPTParams E V L => outputLogits cfg θ x i)
      (paramDomain E V L ε) Kz := fun i => by
    refine LipOn.pi hKz0 fun v => ?_
    have h1 := lipOn_normalized_unembed (E := E) (L := L) hε v
    have h2 := (hlip x hx).apply i
    have h3 := (h1.real_inner h2 (Bf := 1) (Bg := 1) (fun θ _ => norm_normalizeVec_le _)
      (fun θ _ => (norm_hiddenStates cfg θ hx L i).le)
      (div_nonneg zero_le_two hε.le)).const_smul cfg.sZ
    exact h3.mono (le_of_eq (by rw [hKz]; ring))
  have hce : ∀ i ∈ (Finset.univ : Finset ι), LipOn
      (fun θ : NGPTParams E V L => crossEntropy (outputLogits cfg θ x i) (y i))
      (paramDomain E V L ε) (2 * Kz) := fun i _ =>
    (hz i).comp (g := fun z => crossEntropy z (y i)) zero_le_two
      (fun z z' => dist_crossEntropy_le z z' (y i))
  have := (LipOn.sum Finset.univ hce).const_smul (Fintype.card ι : ℝ)⁻¹
  have e : (fun θ : NGPTParams E V L => exampleLoss cfg θ x y) = fun θ =>
      (Fintype.card ι : ℝ)⁻¹ • ∑ i, crossEntropy (outputLogits cfg θ x i) (y i) := by
    funext θ; rw [exampleLoss, smul_eq_mul, div_eq_inv_mul]
  rw [e]
  exact this

omit [Fintype V] in
/-- `paramDomain (ε/2)` is a neighbourhood of every point of `paramDomain ε`. -/
theorem paramDomain_half_mem_nhds [Finite V] {ε : ℝ} (hε : 0 < ε) {θ : NGPTParams E V L}
    (hθ : θ ∈ paramDomain E V L ε) : paramDomain E V L (ε / 2) ∈ 𝓝 θ := by
  have h1 : ∀ᶠ θ' in 𝓝 θ, ∀ l k, ε / 2 < ‖θ'.1 l k‖ :=
    eventually_all.2 fun l => eventually_all.2 fun k =>
      ContinuousAt.eventually_lt continuousAt_const (by fun_prop)
        (by linarith [hθ.1 l k])
  have h2 : ∀ᶠ θ' in 𝓝 θ, ∀ v, ε / 2 < ‖θ'.2 v‖ :=
    eventually_all.2 fun v =>
      ContinuousAt.eventually_lt continuousAt_const (by fun_prop) (by linarith [hθ.2 v])
  filter_upwards [h1, h2] with θ' a b using ⟨fun l k => (a l k).le, fun v => (b v).le⟩

/-- A function that is `M`-Lipschitz on `paramDomain (ε/2)` has derivative of norm at most `M`
at every point of `paramDomain ε`. -/
theorem norm_fderiv_le_of_lipOn_paramDomain {f : NGPTParams E V L → ℝ} {M ε : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (hf : LipOn f (paramDomain E V L (ε / 2)) M) {θ : NGPTParams E V L}
    (hθ : θ ∈ paramDomain E V L ε) : ‖fderiv ℝ f θ‖ ≤ M := by
  have := norm_fderiv_le_of_lipschitzOn ℝ (paramDomain_half_mem_nhds hε hθ)
    hf.to_lipschitzOnWith
  rwa [Real.coe_toNNReal _ hM] at this

/-- **Per-example gradient bound derived from the architecture.** On the domain where every
weight has norm at least `ε > 0`, the gradient of the loss of every example is bounded by a
single constant `M`, uniformly over the parameters and over all examples. This is the
hypothesis `NGPTModel.uniform_grad_bound`, now a theorem about the concrete network. -/
theorem ngpt_exampleLoss_fderiv_bound (cfg : NGPTConfig E) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ι → E, (∀ i, ‖x i‖ = 1) → ∀ y : ι → V,
      ∀ θ ∈ paramDomain E V L ε,
        ‖fderiv ℝ (fun θ' : NGPTParams E V L => exampleLoss cfg θ' x y) θ‖ ≤ M := by
  obtain ⟨M, hM, hlip⟩ := ngpt_exampleLoss_lipOn (ι := ι) (V := V) (L := L) cfg (half_pos hε)
  refine ⟨M + 1, by linarith, fun x hx y θ hθ => ?_⟩
  exact (norm_fderiv_le_of_lipOn_paramDomain hε hM (hlip x hx y) hθ).trans (by linarith)

/-- **Theorem 1 for the concrete architecture.** The empirical risk over any dataset of
(unit-embedded) examples has gradient bounded by one constant `M`, independent of the
parameters in the domain and of the dataset. -/
theorem ngpt_empiricalRisk_fderiv_bound (cfg : NGPTConfig E) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ data : Finset ((ι → E) × (ι → V)), (∀ ex ∈ data, ∀ i, ‖ex.1 i‖ = 1) →
      ∀ θ ∈ paramDomain E V L ε,
        ‖fderiv ℝ (fun θ' : NGPTParams E V L =>
          (∑ ex ∈ data, exampleLoss cfg θ' ex.1 ex.2) / (data.card : ℝ)) θ‖ ≤ M := by
  obtain ⟨M, hM, hlip⟩ := ngpt_exampleLoss_lipOn (ι := ι) (V := V) (L := L) cfg (half_pos hε)
  refine ⟨M + 1, by linarith, fun data hdata θ hθ => ?_⟩
  have hsum := (LipOn.sum data (f := fun ex θ' => exampleLoss cfg θ' ex.1 ex.2)
    (fun ex hex => hlip ex.1 (hdata ex hex) ex.2)).const_smul (data.card : ℝ)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul, abs_inv, Nat.abs_cast] at hsum
  have hle : (data.card : ℝ)⁻¹ * (data.card * M) ≤ M := by
    rcases Nat.eq_zero_or_pos data.card with h0 | hpos
    · rw [h0]; simp [hM]
    · have : (data.card : ℝ) ≠ 0 := by positivity
      rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]
  have e : (fun θ' : NGPTParams E V L =>
      (∑ ex ∈ data, exampleLoss cfg θ' ex.1 ex.2) / (data.card : ℝ)) = fun θ' =>
      (data.card : ℝ)⁻¹ • ∑ ex ∈ data, exampleLoss cfg θ' ex.1 ex.2 := by
    funext θ'; rw [smul_eq_mul, div_eq_inv_mul]
  rw [e]
  exact (norm_fderiv_le_of_lipOn_paramDomain hε hM (hsum.mono hle) hθ).trans (by linarith)

end Network

/-! ### Example: coordinatewise ReLU satisfies the activation hypotheses -/

section ReLU

/-- Coordinatewise ReLU on `ℝ^d`. -/
noncomputable def reluE (d : ℕ) (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => max (v i) 0)

theorem reluE_lipschitz (d : ℕ) : LipschitzWith 1 (reluE d) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, NNReal.coe_one, one_mul]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [reluE, Real.dist_eq, sq_abs]
  rw [← sq_abs, ← sq_abs (u i - v i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs _ _ _) 2

theorem reluE_zero (d : ℕ) : reluE d 0 = 0 := by
  ext i; simp [reluE]

/-- An nGPT configuration on `ℝ^d` with ReLU MLPs. -/
noncomputable def NGPTConfig.relu (d : ℕ) (sQK sZ αA αM : ℝ) (hA0 : 0 ≤ αA) (hA : αA < 1 / 2)
    (hM0 : 0 ≤ αM) (hM : αM < 1 / 2) : NGPTConfig (EuclideanSpace ℝ (Fin d)) where
  sQK := sQK
  sZ := sZ
  alphaA := αA
  alphaM := αM
  alphaA_nonneg := hA0
  alphaA_lt := hA
  alphaM_nonneg := hM0
  alphaM_lt := hM
  act := reluE d
  act_lipschitz := reluE_lipschitz d
  act_zero := reluE_zero d

end ReLU

end BayesianTransformer
