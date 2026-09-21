import Mathlib

/-!
# Operator bounds on algebraic tensor products of inner product spaces

`Mathlib` equips the algebraic tensor product `E ⊗[ℂ] F` of two complex inner product spaces
with an inner product (`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`) and knows that
`TensorProduct.map` of two *isometries* is an isometry, but it does not yet know the basic
**operator bound**

`‖(S ⊗ T) u‖ ≤ ‖S‖ ‖T‖ ‖u‖`

for bounded — not necessarily isometric — factors.  (The file carries an explicit
`TODO: upgrade `map` to a `ContinuousLinearMap`.)  This module supplies the estimate in the
form needed by the second quantization chapters: with explicit bounds `C` for the factors and
no completeness, no finite dimensionality, and — this is the point for the chapters that use
it — **no positivity**: `S` and `T` are arbitrary linear maps satisfying a norm bound, so
their spectra may be unbounded above *and* below.

The proof is the standard orthonormal-expansion argument, which is elementary and needs no
spectral theory:

* every `u : E ⊗[ℂ] F` can be written as `∑ i, x i ⊗ₜ e i` with `(e i)` an **orthonormal**
  finite family in `F` (`exists_orthonormal_repr`); the second factors of any finite
  representation of `u` span a finite-dimensional subspace, in which one picks an orthonormal
  basis;
* such a sum has `‖∑ i, x i ⊗ₜ e i‖² = ∑ i ‖x i‖²` (`norm_sum_tmul_orthonormal`), because the
  cross terms carry the factor `⟪e i, e j⟫ = 0`;
* applying `S` to the first factors therefore multiplies the squared norm by at most `‖S‖²`.

## Contents

* `norm_sum_tmul_orthonormal` — Pythagoras for a sum of tensors with orthonormal right legs.
* `exists_orthonormal_repr` — the orthonormal representation of an arbitrary tensor.
* `norm_map_left_le` — `‖(S ⊗ 1) u‖ ≤ C ‖u‖`.
* `norm_map_right_le` — `‖(1 ⊗ T) u‖ ≤ C ‖u‖`, obtained from the previous one by the
  commutation isometry.
* `norm_map_le` — `‖(S ⊗ T) u‖ ≤ C₁ C₂ ‖u‖`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorOpBound

open scoped TensorProduct

variable {E E' F F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-! ## Orthonormal representation of a tensor -/

/-- **Pythagoras in a tensor product.**  If the right legs `e i` form an orthonormal family,
the squared norm of `∑ i, x i ⊗ₜ e i` is `∑ i ‖x i‖²`. -/
theorem norm_sum_tmul_orthonormal {m : ℕ} (x : Fin m → E) (e : Fin m → F)
    (he : Orthonormal ℂ e) :
    ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have hinner : (inner ℂ (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F) (∑ j, x j ⊗ₜ[ℂ] e j) : ℂ)
      = ∑ i, (inner ℂ (x i) (x i) : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [inner_sum, Finset.sum_eq_single i]
    · simp [he.1 i]
    · intro j _ hji
      rw [TensorProduct.inner_tmul, he.2 (Ne.symm hji)]
      ring
    · intro h; simp at h
  have h1 : ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖ ^ 2
      = (RCLike.re (inner ℂ (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F) (∑ j, x j ⊗ₜ[ℂ] e j) : ℂ)) := by
    rw [inner_self_eq_norm_sq]
  rw [h1, hinner, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [inner_self_eq_norm_sq])

/-- **Every tensor has an orthonormal representation.**  Any `u : E ⊗[ℂ] F` is a finite sum
`∑ i, x i ⊗ₜ e i` whose right legs form an orthonormal family. -/
theorem exists_orthonormal_repr (u : E ⊗[ℂ] F) :
    ∃ (m : ℕ) (x : Fin m → E) (e : Fin m → F), Orthonormal ℂ e ∧ u = ∑ i, x i ⊗ₜ[ℂ] e i := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset u
  set W : Submodule ℂ F := Submodule.span ℂ ((S.image Prod.snd : Finset F) : Set F) with hW
  have hfd : FiniteDimensional ℂ W := by
    rw [hW]; exact FiniteDimensional.span_finset ℂ _
  set b := stdOrthonormalBasis ℂ W with hb
  have hmem : ∀ p ∈ S, p.2 ∈ W := by
    intro p hp
    refine Submodule.subset_span ?_
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.exists, exists_eq_right]
    exact ⟨p.1, hp⟩
  have hrepr : ∀ p ∈ S, ∑ i, (inner ℂ ((b i : F)) p.2 : ℂ) • ((b i : W) : F) = p.2 := by
    intro p hp
    have h := b.sum_repr' (⟨p.2, hmem p hp⟩ : W)
    have h2 := congrArg (fun w : W => (w : F)) h
    simpa using h2
  have hstep : ∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2
      = ∑ p ∈ S, ∑ i, p.1 ⊗ₜ[ℂ] ((inner ℂ ((b i : F)) p.2 : ℂ) • ((b i : W) : F)) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← TensorProduct.tmul_sum, hrepr p hp]
  refine ⟨Module.finrank ℂ W, fun i => ∑ p ∈ S, (inner ℂ ((b i : F)) p.2 : ℂ) • p.1,
    fun i => (b i : F), ?_, ?_⟩
  · rw [show (fun i => ((b i : W) : F)) = (W.subtypeₗᵢ ∘ b) from rfl]
    exact (LinearIsometry.orthonormal_comp_iff W.subtypeₗᵢ).mpr b.orthonormal
  · rw [hS, hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-! ## The operator bounds -/

/-- **Bound for an operator acting on the left factor.**  If `‖S a‖ ≤ C ‖a‖` then
`‖(S ⊗ 1) u‖ ≤ C ‖u‖`.  No positivity, no self-adjointness and no completeness is used. -/
theorem norm_map_left_le (S : E →ₗ[ℂ] E') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : E, ‖S a‖ ≤ C * ‖a‖)
    (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map S (LinearMap.id : F →ₗ[ℂ] F) u‖ ≤ C * ‖u‖ := by
  obtain ⟨m, x, e, he, rfl⟩ := exists_orthonormal_repr u
  have himg : TensorProduct.map S (LinearMap.id : F →ₗ[ℂ] F) (∑ i, x i ⊗ₜ[ℂ] e i)
      = ∑ i, (S (x i)) ⊗ₜ[ℂ] e i := by
    rw [map_sum]; simp
  rw [himg]
  have h1 := norm_sum_tmul_orthonormal (fun i => S (x i)) e he
  have h2 := norm_sum_tmul_orthonormal x e he
  have h3 : ∑ i, ‖S (x i)‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := hC (x i)
    nlinarith [norm_nonneg (S (x i)), norm_nonneg (x i)]
  have hsq : ‖(∑ i, (S (x i)) ⊗ₜ[ℂ] e i : E' ⊗[ℂ] F)‖ ^ 2
      ≤ (C * ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖) ^ 2 := by
    rw [h1, mul_pow, h2]; exact h3
  have hn1 := norm_nonneg (∑ i, (S (x i)) ⊗ₜ[ℂ] e i : E' ⊗[ℂ] F)
  have hn2 := norm_nonneg (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)
  nlinarith [mul_nonneg hC0 hn2]

/-- The commutation isometry intertwines an operator on the right factor with the same
operator on the left factor. -/
theorem comm_map_id (T : F →ₗ[ℂ] F') (u : E ⊗[ℂ] F) :
    TensorProduct.comm ℂ E F' (TensorProduct.map LinearMap.id T u)
      = TensorProduct.map T (LinearMap.id : E →ₗ[ℂ] E) (TensorProduct.comm ℂ E F u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp [hs, ht]

/-- **Bound for an operator acting on the right factor.** -/
theorem norm_map_right_le (T : F →ₗ[ℂ] F') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ b : F, ‖T b‖ ≤ C * ‖b‖)
    (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖ ≤ C * ‖u‖ := by
  have h1 : ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖
      = ‖TensorProduct.comm ℂ E F' (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u)‖ := by
    rw [TensorProduct.norm_comm]
  rw [h1, comm_map_id T u]
  have h2 := norm_map_left_le (F := E) T hC0 hC (TensorProduct.comm ℂ E F u)
  rwa [TensorProduct.norm_comm] at h2

/-- **The operator bound on a tensor product.**  For arbitrary bounded (in particular,
possibly indefinite) factors, `‖(S ⊗ T) u‖ ≤ C₁ C₂ ‖u‖`. -/
theorem norm_map_le (S : E →ₗ[ℂ] E') (T : F →ₗ[ℂ] F') {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hS : ∀ a : E, ‖S a‖ ≤ C₁ * ‖a‖) (hT : ∀ b : F, ‖T b‖ ≤ C₂ * ‖b‖) (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map S T u‖ ≤ C₁ * C₂ * ‖u‖ := by
  have hfac : TensorProduct.map S T u
      = TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u) := by
    have : TensorProduct.map S T
        = (TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')) ∘ₗ
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T) := by
      rw [← TensorProduct.map_comp]; simp
    exact congrArg (fun L : (E ⊗[ℂ] F) →ₗ[ℂ] (E' ⊗[ℂ] F') => L u) this
  rw [hfac]
  calc ‖TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u)‖
      ≤ C₁ * ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖ :=
        norm_map_left_le S hC₁ hS _
    _ ≤ C₁ * (C₂ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_map_right_le T hC₂ hT u) hC₁
    _ = C₁ * C₂ * ‖u‖ := by ring

end BookProof.TensorOpBound
