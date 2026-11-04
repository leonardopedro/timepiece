module

public import Mathlib

/-!
# Unbounded Hamiltonians and the shift-invert (SIRK) setting

The files `ArtificialGap.lean` and `NestedFock.lean` state their results for bounded operators.
This file restates the parts of the argument that matter for the pipeline of answer A and the
regulator of answer B for an **unbounded** Hamiltonian. Such an operator is modelled as a
partially defined linear map `H : E →ₗ.[ℂ] E` (Mathlib's `LinearPMap`), with domain `H.domain`.
The shift-invert operator of SIRK is a *bounded* operator `R : E →L[ℂ] E` that inverts
`H - σ` (predicate `IsShiftInvert`).

* `shiftInvert_eigen_of_eigen`, `eigen_of_shiftInvert_eigen`: eigenpairs of `R` and of `H`
  correspond under `ν ↦ σ + 1/ν`. So the numerics run on the bounded `R`, and their output says
  something about the unbounded `H`.
* `temple_lower_bound_unbounded`, `temple_enclosure_converges_unbounded`: Temple's inequality
  and the shrinking enclosure of Step 3, for trial vectors in the domain of `H`.
* `separation_input_is_gap_unbounded`, `step3_hypothesis_implies_gap_unbounded`: the
  separation input of Step 3 already implies the gap, also for unbounded `H`.
* `shifted_shiftInvert_on_sector`: on a sector `N = n`, the shift-invert operator of
  `H + μN` at `z` equals the shift-invert operator of `H` at `z - μn`. So in the sector of the
  physical vacuum the regulator only moves the shift.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `R` is the shift-invert operator `(H - σ)⁻¹` of the (possibly unbounded) operator `H`
at the shift `σ`: `R` maps into the domain of `H`, `(H - σ) R = 1` on `E`, and
`R (H - σ) = 1` on the domain of `H`. `R` itself is bounded. -/
structure IsShiftInvert (H : E →ₗ.[ℂ] E) (σ : ℂ) (R : E →L[ℂ] E) : Prop where
  mem_domain : ∀ x : E, R x ∈ H.domain
  right_inv : ∀ x : E, H ⟨R x, mem_domain x⟩ - σ • R x = x
  left_inv : ∀ y : H.domain, R (H y - σ • (y : E)) = y

/-- An eigenvector of `H` with eigenvalue `l ≠ σ` is an eigenvector of the shift-invert
operator `R = (H - σ)⁻¹` with eigenvalue `(l - σ)⁻¹`. -/
theorem shiftInvert_eigen_of_eigen {H : E →ₗ.[ℂ] E} {σ : ℂ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert H σ R) (y : H.domain) (l : ℂ) (hl : l ≠ σ)
    (hy : H y = l • (y : E)) : R y = (l - σ)⁻¹ • (y : E) := by
  have h := hR.left_inv y
  rw [hy, ← sub_smul, map_smul] at h
  have hne : l - σ ≠ 0 := sub_ne_zero.mpr hl
  calc R y = (l - σ)⁻¹ • ((l - σ) • R y) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (l - σ)⁻¹ • (y : E) := by rw [h]

/-- Conversely, an eigenvector of the bounded shift-invert operator `R` with eigenvalue `ν ≠ 0`
lies in the domain of `H` and is an eigenvector of `H` with eigenvalue `σ + 1/ν`. -/
theorem eigen_of_shiftInvert_eigen {H : E →ₗ.[ℂ] E} {σ : ℂ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert H σ R) (x : E) (ν : ℂ) (hν : ν ≠ 0) (hx : R x = ν • x) :
    ∃ hdom : x ∈ H.domain, H ⟨x, hdom⟩ = (σ + ν⁻¹) • x := by
  have hxeq : x = ν⁻¹ • R x := by rw [hx, smul_smul, inv_mul_cancel₀ hν, one_smul]
  have hdom : x ∈ H.domain := by
    rw [hxeq]; exact H.domain.smul_mem _ (hR.mem_domain x)
  refine ⟨hdom, ?_⟩
  have h1 := hR.right_inv x
  have h2 : (⟨x, hdom⟩ : H.domain) = ν⁻¹ • ⟨R x, hR.mem_domain x⟩ := by
    ext; simpa using hxeq
  have h3 : H ⟨R x, hR.mem_domain x⟩ = x + σ • R x := eq_add_of_sub_eq h1
  rw [h2, LinearPMap.map_smul, h3, hx, smul_add, smul_smul, smul_smul, add_smul,
    show ν⁻¹ * σ * ν = σ by field_simp]
  abel

/-- **Temple's inequality for an unbounded `H`.** If the spectrum of `H` avoids `(l₀, β)`,
expressed as `Re ⟪(H - β)x, (H - l₀)x⟫ ≥ 0` for every `x` in the domain, then for every unit
trial vector `ψ` in the domain with `θ = Re ⟪ψ, Hψ⟫ < β` we have
`θ - ‖Hψ - θψ‖²/(β - θ) ≤ l₀`. -/
theorem temple_lower_bound_unbounded (H : E →ₗ.[ℂ] E) (l₀ β : ℝ)
    (hspec : ∀ x : H.domain, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • (x : E), H x - (l₀ : ℂ) • (x : E)⟫_ℂ)
    (ψ : H.domain) (hψ : ‖(ψ : E)‖ = 1) (hθ : RCLike.re ⟪(ψ : E), H ψ⟫_ℂ < β) :
    RCLike.re ⟪(ψ : E), H ψ⟫_ℂ
      - ‖H ψ - ((RCLike.re ⟪(ψ : E), H ψ⟫_ℂ : ℝ) : ℂ) • (ψ : E)‖ ^ 2
        / (β - RCLike.re ⟪(ψ : E), H ψ⟫_ℂ) ≤ l₀ := by
  set θ := RCLike.re ⟪(ψ : E), H ψ⟫_ℂ with hθdef
  set u : E := (ψ : E) with hu
  have hconj : RCLike.re ⟪H ψ, u⟫_ℂ = θ := by
    rw [hθdef, ← inner_conj_symm, RCLike.conj_re]
  have hψψ : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [hψ]
  have key : ∀ (a b : ℝ), RCLike.re ⟪H ψ - (a : ℂ) • u, H ψ - (b : ℂ) • u⟫_ℂ
      = ‖H ψ‖ ^ 2 - (a + b) * θ + a * b := by
    intro a b
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, map_sub, hψψ,
      inner_self_eq_norm_sq_to_K]
    simp only [RCLike.re_to_complex] at hconj hθdef ⊢
    simp [Complex.mul_re, hconj, ← hθdef, ← Complex.ofReal_pow]
    ring
  have hη : ‖H ψ - (θ : ℂ) • u‖ ^ 2 = ‖H ψ‖ ^ 2 - θ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), key]; ring
  have hs := hspec ψ
  rw [key] at hs
  rw [hη]
  have hpos : 0 < β - θ := by linarith
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hpos]
  nlinarith

/-- **Shrinking enclosure (Step 3) for an unbounded `H`.** For trial vectors `ψ m` in the domain
with a uniform separation `β - θ_m ≥ c > 0` and residuals `‖Hψ_m - θ_mψ_m‖ → 0`, the Rayleigh
quotients `θ_m` converge to the ground energy `l₀`. -/
theorem temple_enclosure_converges_unbounded (H : E →ₗ.[ℂ] E) (l₀ β c : ℝ) (hc : 0 < c)
    (hspec : ∀ x : H.domain, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • (x : E), H x - (l₀ : ℂ) • (x : E)⟫_ℂ)
    (hbot : ∀ x : H.domain, l₀ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (ψ : ℕ → H.domain) (hψ : ∀ m, ‖(ψ m : E)‖ = 1)
    (hsep : ∀ m, c ≤ β - RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ)
    (hres : Filter.Tendsto
      (fun m => ‖H (ψ m) - ((RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ : ℝ) : ℂ) • (ψ m : E)‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ) Filter.atTop (nhds l₀) := by
  have hup : Filter.Tendsto
      (fun m => l₀ + ‖H (ψ m) - ((RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ : ℝ) : ℂ) • (ψ m : E)‖ ^ 2 / c)
      Filter.atTop (nhds l₀) := by
    simpa using tendsto_const_nhds.add ((hres.pow 2).div_const c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_)
    (fun m => ?_)
  · simpa [hψ m] using hbot (ψ m)
  · have hpos : 0 < β - RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ := lt_of_lt_of_le hc (hsep m)
    have ht := temple_lower_bound_unbounded H l₀ β hspec (ψ m) (hψ m) (by linarith)
    have : ‖H (ψ m) - ((RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ : ℝ) : ℂ) • (ψ m : E)‖ ^ 2
          / (β - RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ)
        ≤ ‖H (ψ m) - ((RCLike.re ⟪(ψ m : E), H (ψ m)⟫_ℂ : ℝ) : ℂ) • (ψ m : E)‖ ^ 2 / c := by
      gcongr; exact hsep m
    simp only
    linarith

/-- The separation hypothesis (spectrum avoids `(l₀, β)`) for an unbounded `H` forces every
eigenvalue `e > l₀` to satisfy `e ≥ β`. -/
theorem separation_input_is_gap_unbounded (H : E →ₗ.[ℂ] E) (l₀ β : ℝ)
    (hspec : ∀ x : H.domain, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • (x : E), H x - (l₀ : ℂ) • (x : E)⟫_ℂ)
    (v : H.domain) (hv : (v : E) ≠ 0) (e : ℝ) (hev : H v = (e : ℂ) • (v : E)) (he : l₀ < e) :
    β ≤ e := by
  have h := hspec v
  rw [hev, ← sub_smul, ← sub_smul, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at h
  have hn : 0 < ‖(v : E)‖ ^ 2 := by positivity
  have : RCLike.re ((starRingEnd ℂ) ((e : ℂ) - β) * (((e : ℂ) - l₀) * ((‖(v : E)‖ : ℂ) ^ 2)))
      = (e - β) * (e - l₀) * ‖(v : E)‖ ^ 2 := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]; ring
  have h2 : 0 ≤ (e - β) * (e - l₀) * ‖(v : E)‖ ^ 2 := by convert h using 1; exact this.symm
  by_contra hlt
  push Not at hlt
  have : (e - β) * (e - l₀) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith

/-- **Step 3 already contains the gap, also for unbounded `H`.** Under the separation input
(`β - θ ≥ c` for some unit trial vector in the domain, `l₀` the ground energy), every eigenvalue
of `H` above `l₀` lies at least `c` above it. -/
theorem step3_hypothesis_implies_gap_unbounded (H : E →ₗ.[ℂ] E) (l₀ β c : ℝ)
    (hspec : ∀ x : H.domain, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • (x : E), H x - (l₀ : ℂ) • (x : E)⟫_ℂ)
    (hbot : ∀ x : H.domain, l₀ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (ψ : H.domain) (hψ : ‖(ψ : E)‖ = 1) (hsep : c ≤ β - RCLike.re ⟪(ψ : E), H ψ⟫_ℂ)
    (v : H.domain) (hv : (v : E) ≠ 0) (e : ℝ) (hev : H v = (e : ℂ) • (v : E)) (he : l₀ < e) :
    c ≤ e - l₀ := by
  have h1 := separation_input_is_gap_unbounded H l₀ β hspec v hv e hev he
  have h2 : l₀ ≤ RCLike.re ⟪(ψ : E), H ψ⟫_ℂ := by simpa [hψ] using hbot ψ
  linarith

/-- **The regulator only moves the shift on a sector.** Let `H` and `N` be unbounded, let
`Hμ` be an operator that equals `H + μN` on the common domain, and let `Rμ` be its shift-invert
operator at `z` and `R₀` the shift-invert operator of `H` at `z - μn`. If `ψ` lies in the sector
`N = n`, in the sense that `R₀ψ` is in the domain of `N` with `N(R₀ψ) = n R₀ψ` (this holds when
`R₀` preserves the sector, e.g. when `H` commutes with `N`), then `Rμ ψ = R₀ ψ`.
So in the sector of the physical vacuum, the shift-invert operator of `H + μN` is an ordinary
shift-invert operator of `H`. -/
theorem shifted_shiftInvert_on_sector (H N Hμ : E →ₗ.[ℂ] E) (μ n : ℝ) (z : ℂ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩)
    (Rμ R₀ : E →L[ℂ] E) (hRμ : IsShiftInvert Hμ z Rμ)
    (hR₀ : IsShiftInvert H (z - (μ * n : ℝ)) R₀)
    (ψ : E) (hNdom : R₀ ψ ∈ N.domain) (hsector : N ⟨R₀ ψ, hNdom⟩ = (n : ℂ) • R₀ ψ) :
    Rμ ψ = R₀ ψ := by
  have hHdom := hR₀.mem_domain ψ
  have h1 := hRμ.left_inv ⟨R₀ ψ, hdom _ hHdom hNdom⟩
  simp only at h1
  rw [hsum _ hHdom hNdom, hsector] at h1
  have h2 := hR₀.right_inv ψ
  have h3 : H ⟨R₀ ψ, hHdom⟩ + (μ : ℂ) • ((n : ℂ) • R₀ ψ) - z • R₀ ψ
      = H ⟨R₀ ψ, hR₀.mem_domain ψ⟩ - (z - ((μ * n : ℝ) : ℂ)) • R₀ ψ := by
    rw [smul_smul, sub_smul]; push_cast; abel
  rw [h3, h2] at h1
  exact h1

end CftCheck
