import Mathlib
import BookProof.Toolbox.ChapterFockGramSchmidtProjection
import BookProof.ChapterQuadraticFockEsa

/-!
# The monomial–Hermite triangularity and the `coreBasis`/`hermBasisN` bridge

`BookProof.FockGramSchmidtProjection` reduced the bridge between the Gram–Schmidt basis
`coreBasis e` of `L²(ℝᵈ)` and the enumerated product Hermite basis `hermBasisN e` to two
inputs: the decomposition

`x^{e k} e^{-‖x‖²/4} = w + c • ψ_{e k}`,  `w` in the earlier Gram–Schmidt span,

and a modulus statement for the coefficient.  This module supplies both, and concludes that
the two bases are in fact *equal*.

## Contents

* `DegreeCompatible e` — the enumeration of the multi-indices lists every multi-index of
  smaller total degree before a given one.  This is the hypothesis under which the earlier
  monomials are exactly the earlier basis vectors; it implies the coordinatewise-smaller
  hypothesis that the vanishing lemma of `BookProof.HermiteVanishing` consumes
  (`DegreeCompatible.exists_lt_apply`) and the monotonicity of the total degree along the
  enumeration (`DegreeCompatible.degree_mono`);
* `monomialSpan d n` — the span of the monomials of total degree `< n`, and
  `monomial_sub_hermiteMv_mem` — **the triangularity**: `x^α − He_α` is a combination of
  monomials of total degree `< |α|`.  This is proved from the three-term recurrence
  `hermiteMv_X_mul` alone: no monicity of `He_n` is needed, because the recurrence already
  records that the leading monomial of `He_α` is `x^α`;
* `monomialSpanLp d n`, `pgLp_mem_monomialSpanLp`, `monomialSpanLp_le_gsSpan` — the same
  span inside `L²(ℝᵈ)`, and its identification with the earlier Gram–Schmidt span under
  `DegreeCompatible`;
* `coreFamily_sub_hermiteMvLp_mem` — **the decomposition**
  `f k − ‖ψ_{e k}‖ • ψ_{e k} ∈ gsSpan f k`, i.e. `x^{e k} e^{-‖x‖²/4} = w + c • ψ_{e k}`
  with `w` in the earlier span and `c = ‖ψ_{e k}‖ ≠ 0`;
* `norm_hermiteMvLp` — the coefficient has modulus one *after normalization*:
  `‖ψ_{e k}‖ = 1`;
* `gramSchmidtNormed_eq_phase_of_decomp` — for **any** unit vector `g` realising the
  orthogonal direction, the normalized Gram–Schmidt vector is a unit-modulus phase times
  `g`;
* `gramSchmidt_coreFamily_eq`, `coreBasis_eq_hermBasisN` — the Gram–Schmidt vector of the
  monomial family **is** the product Hermite function, and the two orthonormal bases
  coincide: `coreBasis e k = hermBasisN e k` for every `k`, with phase `1`.

## Honest boundary

`DegreeCompatible` is a hypothesis on the enumeration: it says the enumeration is sorted by
nondecreasing total degree and lists every multi-index of smaller degree.  Nothing here
constructs such an enumeration (this is a counting argument on `Fin d →₀ ℕ`, independent of
the analysis); what is proved is that *given* one, the bridge closes with no phase at all.
Note also that the bridge only compares the two bases level by level — it does not identify
the operators on the two finite-mode domains beyond what `BookProof.YangMillsCoreBasisGates`
already transports.
-/

namespace BookProof.HermiteBridgePhases

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FockGramSchmidtProjection InnerProductSpace BookProof.QuadFockEsa

noncomputable section

variable {d : ℕ}

/-! ## Degree-compatible enumerations -/

/-- **A degree-compatible enumeration of the multi-indices**: every multi-index whose total
degree is smaller than that of `e k` occurs strictly before `k`. -/
def DegreeCompatible (e : ℕ ≃ (Fin d →₀ ℕ)) : Prop :=
  ∀ k b, (∑ i, b i) < (∑ i, e k i) → ∃ j < k, e j = b

/-- Under a degree-compatible enumeration the total degree is monotone. -/
theorem DegreeCompatible.degree_mono {e : ℕ ≃ (Fin d →₀ ℕ)} (he : DegreeCompatible e)
    {j k : ℕ} (hjk : j < k) : (∑ i, e j i) ≤ ∑ i, e k i := by
  by_contra hle
  push_neg at hle
  obtain ⟨i, hi, hie⟩ := he j (e k) hle
  have hik : i = k := e.injective hie
  omega

/-- A degree-compatible enumeration satisfies the coordinatewise hypothesis of the vanishing
lemma: every earlier multi-index is strictly smaller in some coordinate. -/
theorem DegreeCompatible.exists_lt_apply {e : ℕ ≃ (Fin d →₀ ℕ)} (he : DegreeCompatible e)
    {j k : ℕ} (hjk : j < k) : ∃ i, e j i < e k i := by
  by_contra h
  push_neg at h
  have hne : e j ≠ e k := e.injective.ne (by omega)
  have hstrict : ∃ i, e k i < e j i := by
    by_contra hno
    push_neg at hno
    exact hne (Finsupp.ext fun i => le_antisymm (hno i) (h i))
  obtain ⟨i, hi⟩ := hstrict
  have hlt : (∑ i, e k i) < ∑ i, e j i :=
    Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ i, hi⟩
  exact absurd hlt (not_lt.mpr (he.degree_mono hjk))

/-! ## Total degree arithmetic on multi-indices -/

/-- The sum of a single-coordinate multi-index. -/
theorem sum_single_apply (i : Fin d) (c : ℕ) : (∑ j, Finsupp.single i c j) = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact Finsupp.single_eq_of_ne hj
  · intro hi
    simp at hi

/-- The total degree increases by one when a coordinate is raised by one. -/
theorem sum_add_single (b : Fin d →₀ ℕ) (i : Fin d) :
    (∑ j, (b + Finsupp.single i (1 : ℕ)) j) = (∑ j, b j) + 1 := by
  have hpt : ∀ j, (b + Finsupp.single i (1 : ℕ)) j = b j + Finsupp.single i (1 : ℕ) j :=
    fun j => Finsupp.add_apply b (Finsupp.single i (1 : ℕ)) j
  simp only [hpt]
  rw [Finset.sum_add_distrib, sum_single_apply]

/-- The total degree decreases by one when a non-zero coordinate is lowered by one. -/
theorem sum_sub_single {b : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ b i) :
    (∑ j, (b - Finsupp.single i (1 : ℕ)) j) = (∑ j, b j) - 1 := by
  have hpt : ∀ j, (b - Finsupp.single i (1 : ℕ)) j = b j - Finsupp.single i (1 : ℕ) j :=
    fun j => Finsupp.tsub_apply b (Finsupp.single i (1 : ℕ)) j
  set S := ∑ j ∈ Finset.univ.erase i, b j with hS
  have h1 : (∑ j, b j) = b i + S := by
    rw [hS]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have h2 : (∑ j, (b - Finsupp.single i (1 : ℕ)) j) = (b i - 1) + S := by
    have hs : (∑ j ∈ Finset.univ.erase i, (b - Finsupp.single i (1 : ℕ)) j) = S := by
      rw [hS]
      exact Finset.sum_congr rfl fun j hj => by
        rw [hpt, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), Nat.sub_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hs]
    congr 1
    rw [hpt]
    simp
  rw [h2, h1]
  omega

/-! ## The span of the monomials of small degree -/

/-- The span of the monomials of total degree `< n`. -/
def monomialSpan (d : ℕ) (n : ℕ) : Submodule ℂ (MvPolynomial (Fin d) ℂ) :=
  Submodule.span ℂ
    {p | ∃ b : Fin d →₀ ℕ, (∑ i, b i) < n ∧ p = MvPolynomial.monomial b (1 : ℂ)}

/-- Every monomial of total degree `< n` lies in the span. -/
theorem monomial_mem_monomialSpan {n : ℕ} {b : Fin d →₀ ℕ} (h : (∑ i, b i) < n) :
    MvPolynomial.monomial b (1 : ℂ) ∈ monomialSpan d n :=
  Submodule.subset_span ⟨b, h, rfl⟩

theorem monomialSpan_mono {m n : ℕ} (h : m ≤ n) : monomialSpan d m ≤ monomialSpan d n := by
  rw [monomialSpan, monomialSpan, Submodule.span_le]
  rintro p ⟨b, hb, rfl⟩
  exact monomial_mem_monomialSpan (lt_of_lt_of_le hb h)

/-- A polynomial of total degree `< n` lies in the span of the monomials of degree `< n`. -/
theorem mem_monomialSpan_of_totalDegree_lt {p : MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hp : p.totalDegree < n) : p ∈ monomialSpan d n := by
  have hsum : p = ∑ v ∈ p.support, (MvPolynomial.monomial v) (MvPolynomial.coeff v p) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun v hv => ?_
  have hvdeg : v.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hv
  have hvsum : (∑ i, v i) ≤ p.totalDegree := by
    have h := hvdeg
    rw [Finsupp.sum_fintype (f := v) (g := fun _ e => e) (fun _ => rfl)] at h
    simpa using h
  have hcoe : (MvPolynomial.monomial v) (MvPolynomial.coeff v p)
      = MvPolynomial.coeff v p • MvPolynomial.monomial v (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hcoe]
  exact Submodule.smul_mem _ _ (monomial_mem_monomialSpan (lt_of_le_of_lt hvsum hp))

/-- Multiplying a vector of the span by a coordinate stays in the next span. -/
theorem mul_X_mem_monomialSpan {i : Fin d} {m : ℕ} {q : MvPolynomial (Fin d) ℂ}
    (hq : q ∈ monomialSpan d m) :
    (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) * q ∈ monomialSpan d (m + 1) := by
  refine Submodule.span_induction
    (p := fun q _ => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) * q ∈ monomialSpan d (m + 1))
    ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨b, hb, rfl⟩
    have hX : (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)
        = MvPolynomial.monomial (Finsupp.single i (1 : ℕ)) (1 : ℂ) := by
      simp [MvPolynomial.X]
    rw [hX, MvPolynomial.monomial_mul, one_mul]
    refine monomial_mem_monomialSpan ?_
    rw [add_comm (Finsupp.single i (1 : ℕ)) b, sum_add_single]
    omega
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

/-- **The monomial–Hermite triangularity**: `x^α − He_α` is a combination of monomials of
total degree `< |α|`.  Proved by strong induction on the total degree from the three-term
recurrence, which is what makes `He_α` monic without a separate monicity statement. -/
theorem monomial_sub_hermiteMv_mem (a : Fin d →₀ ℕ) :
    MvPolynomial.monomial a (1 : ℂ) - hermiteMv a ∈ monomialSpan d (∑ i, a i) := by
  classical
  suffices H : ∀ n : ℕ, ∀ a : Fin d →₀ ℕ, (∑ i, a i) = n →
      MvPolynomial.monomial a (1 : ℂ) - hermiteMv a ∈ monomialSpan d n from H _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    by_cases hzero : a = 0
    · subst hzero
      have hmon : MvPolynomial.monomial (0 : Fin d →₀ ℕ) (1 : ℂ) = 1 := by
        have h := MvPolynomial.monomial_zero' (R := ℂ) (σ := Fin d)
        exact (congrFun h (1 : ℂ)).trans MvPolynomial.C_1
      rw [hmon, hermiteMv_zero, sub_self]
      exact Submodule.zero_mem _
    · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hzero (Finsupp.ext hc)
      have hpos : 1 ≤ a i := Nat.one_le_iff_ne_zero.mpr hi
      have hnpos : 1 ≤ n := by
        rw [← ha]
        calc 1 ≤ a i := hpos
          _ ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      set b : Fin d →₀ ℕ := a - Finsupp.single i (1 : ℕ) with hbdef
      have hba : b + Finsupp.single i (1 : ℕ) = a := by
        rw [hbdef]
        ext j
        by_cases hj : j = i
        · subst hj
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hj]
      have hbdeg : (∑ j, b j) = n - 1 := by
        rw [hbdef, sum_sub_single hpos, ha]
      have hqb : MvPolynomial.monomial b (1 : ℂ) - hermiteMv b ∈ monomialSpan d (n - 1) :=
        ih (n - 1) (by omega) b hbdeg
      have hXq : (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)
            * (MvPolynomial.monomial b (1 : ℂ) - hermiteMv b) ∈ monomialSpan d n := by
        have := mul_X_mem_monomialSpan (i := i) hqb
        rwa [Nat.sub_add_cancel hnpos] at this
      have hsm : ((b i : ℕ) : ℂ) • hermiteMv (b - Finsupp.single i (1 : ℕ)) ∈
          monomialSpan d n := by
        by_cases h0 : b i = 0
        · have hz : ((b i : ℕ) : ℂ) = 0 := by rw [h0]; simp
          rw [hz, zero_smul]
          exact Submodule.zero_mem _
        · have hbi : 0 < b i := Nat.pos_of_ne_zero h0
          set c : Fin d →₀ ℕ := b - Finsupp.single i (1 : ℕ) with hcdef
          have hcdeg : (∑ j, c j) = (n - 1) - 1 := by
            rw [hcdef, sum_sub_single hbi, hbdeg]
          have hqc : MvPolynomial.monomial c (1 : ℂ) - hermiteMv c
              ∈ monomialSpan d ((n - 1) - 1) := ih _ (by omega) c hcdeg
          have hmonc : MvPolynomial.monomial c (1 : ℂ) ∈ monomialSpan d n :=
            monomial_mem_monomialSpan (by omega)
          have hhermc : hermiteMv c ∈ monomialSpan d n := by
            have hsplit : MvPolynomial.monomial c (1 : ℂ)
                - (MvPolynomial.monomial c (1 : ℂ) - hermiteMv c) = hermiteMv c := by abel
            rw [← hsplit]
            exact Submodule.sub_mem _ hmonc (monomialSpan_mono (by omega) hqc)
          exact Submodule.smul_mem _ _ hhermc
      have hkey : MvPolynomial.monomial a (1 : ℂ) - hermiteMv a
          = ((b i : ℕ) : ℂ) • hermiteMv (b - Finsupp.single i (1 : ℕ))
            + (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)
              * (MvPolynomial.monomial b (1 : ℂ) - hermiteMv b) := by
        have hmon : (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) * MvPolynomial.monomial b 1
            = MvPolynomial.monomial a (1 : ℂ) := by
          rw [show (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)
              = MvPolynomial.monomial (Finsupp.single i (1 : ℕ)) (1 : ℂ) from by
                simp [MvPolynomial.X],
            MvPolynomial.monomial_mul, one_mul, add_comm (Finsupp.single i (1 : ℕ)) b, hba]
        have hrec : hermiteMv (b + Finsupp.single i (1 : ℕ))
            = (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) * hermiteMv b
              - ((b i : ℕ) : ℂ) • hermiteMv (b - Finsupp.single i (1 : ℕ)) := by
          rw [hermiteMv_X_mul i b]
          abel
        rw [← hmon, ← hba, hrec]
        ring
      rw [hkey]
      exact Submodule.add_mem _ hsm hXq

/-! ## The same span inside `L²(ℝᵈ)` -/

/-- The `L²` span of the Gauss monomials of total degree `< n`. -/
def monomialSpanLp (d : ℕ) (n : ℕ) : Submodule ℂ (L2d d) :=
  Submodule.span ℂ
    {x | ∃ b : Fin d →₀ ℕ, (∑ i, b i) < n ∧ x = pgLp (MvPolynomial.monomial b (1 : ℂ))}

theorem pgLp_mem_monomialSpanLp {p : MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hp : p ∈ monomialSpan d n) : pgLp p ∈ monomialSpanLp d n := by
  refine Submodule.span_induction (p := fun p _ => pgLp p ∈ monomialSpanLp d n) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨b, hb, rfl⟩
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  · change pgLp (0 : MvPolynomial (Fin d) ℂ) ∈ monomialSpanLp d n
    have h0 : pgLp (0 : MvPolynomial (Fin d) ℂ) = 0 := by
      rw [← HermiteProductCore.pgMap_apply, map_zero]
    rw [h0]
    exact Submodule.zero_mem (monomialSpanLp d n)
  · intro x y _ _ hx hy
    have h : pgLp (x + y) = pgLp x + pgLp y := by
      rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply,
        ← HermiteProductCore.pgMap_apply, map_add]
    rw [h]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have h : pgLp (c • x) = c • pgLp x := by
      rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply, map_smul]
    rw [h]
    exact Submodule.smul_mem _ _ hx

/-- Under a degree-compatible enumeration, the small-degree monomial span is contained in the
earlier Gram–Schmidt span. -/
theorem monomialSpanLp_le_gsSpan (e : ℕ ≃ (Fin d →₀ ℕ)) (hdeg : DegreeCompatible e)
    (k : ℕ) : monomialSpanLp d (∑ i, e k i) ≤ gsSpan (coreFamily e) k := by
  rw [monomialSpanLp, Submodule.span_le]
  rintro x ⟨b, hb, rfl⟩
  obtain ⟨j, hj, hje⟩ := hdeg k b hb
  have hx : pgLp (MvPolynomial.monomial b (1 : ℂ)) = coreFamily e j := by
    rw [coreFamily_apply, hje]
  rw [gsSpan_eq_span_Iio, hx]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

/-! ## The orthogonal decomposition and the unit-modulus phase -/

/-- **The decomposition** `x^{e k} e^{-‖x‖²/4} = w + ‖ψ_{e k}‖ • ψ_{e k}` with `w` in the
earlier Gram–Schmidt span. -/
theorem coreFamily_sub_hermiteMvLp_mem (e : ℕ ≃ (Fin d →₀ ℕ)) (hdeg : DegreeCompatible e)
    (k : ℕ) :
    coreFamily e k - ((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k)
      ∈ gsSpan (coreFamily e) k := by
  have hdecomp : coreFamily e k - ((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k)
      = pgLp (MvPolynomial.monomial (e k) (1 : ℂ) - hermiteMv (e k)) := by
    have h1 : pgLp (MvPolynomial.monomial (e k) (1 : ℂ)) - pgLp (hermiteMv (e k))
        = pgLp (MvPolynomial.monomial (e k) (1 : ℂ) - hermiteMv (e k)) := by
      rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply,
        ← HermiteProductCore.pgMap_apply, map_sub]
    rw [coreFamily_apply, ← pgLp_hermiteMv_eq (e k), h1]
  rw [hdecomp]
  exact monomialSpanLp_le_gsSpan e hdeg k
    (pgLp_mem_monomialSpanLp (monomial_sub_hermiteMv_mem (e k)))

/-- The product Hermite functions are unit vectors. -/
theorem norm_hermiteMvLp (a : Fin d →₀ ℕ) : ‖hermiteMvLp a‖ = 1 := by
  have hinner : (inner ℂ (hermiteMvLp a) (hermiteMvLp a) : ℂ) = 1 := by
    simpa using inner_hermiteMvLp a a
  have hsq : ‖hermiteMvLp a‖ ^ 2 = (1 : ℝ) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hermiteMvLp a), hinner]
    simp
  nlinarith [norm_nonneg (hermiteMvLp a)]

/-- **The Gram–Schmidt vector of the monomial family is the product Hermite function**, with
the norm of the un-normalized Hermite function as coefficient. -/
theorem gramSchmidt_coreFamily_eq (e : ℕ ≃ (Fin d →₀ ℕ)) (hdeg : DegreeCompatible e)
    (k : ℕ) :
    InnerProductSpace.gramSchmidt ℂ (coreFamily e) k
      = ((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k) :=
  gramSchmidt_eq_smul_of_decomp
    (hermiteMvLp_mem_orthogonal_gsSpan e (k := k) (fun _ hj => hdeg.exists_lt_apply hj))
    (coreFamily_sub_hermiteMvLp_mem e hdeg k)

/-- **The modulus of the coefficient, after normalization is one.**  For any unit vector `g`
realising the orthogonal direction of `f k` modulo the earlier span, with a non-zero
coefficient `c`, the *normalized* Gram–Schmidt vector is a unit-modulus phase times `g`. -/
theorem gramSchmidtNormed_eq_phase_of_decomp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f : ℕ → E} {k : ℕ} {g : E} {c : ℂ}
    (hg : g ∈ (gsSpan f k)ᗮ) (hdec : f k - c • g ∈ gsSpan f k) (hgn : ‖g‖ = 1)
    (hc : c ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ gramSchmidtNormed ℂ f k = u • g := by
  refine ⟨((‖c‖ : ℝ) : ℂ)⁻¹ * c, ?_, ?_⟩
  · have hne : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr hc
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]
  · have hgs := gramSchmidt_eq_smul_of_decomp hg hdec
    rw [gramSchmidtNormed, hgs, norm_smul, hgn, mul_one, smul_smul]
    rfl

/-- **The bridge**: under a degree-compatible enumeration the Gram–Schmidt basis of the
monomial family is *equal* to the enumerated product Hermite basis, level by level. -/
theorem coreBasis_eq_hermBasisN (e : ℕ ≃ (Fin d →₀ ℕ)) (hdeg : DegreeCompatible e) (k : ℕ) :
    coreBasis e k = hermBasisN e k := by
  rw [coreBasis, HilbertBasis.coe_mk, hermBasisN_apply, gramSchmidtNormed,
    gramSchmidt_coreFamily_eq e hdeg k]
  have hnorm : ‖((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k)‖ = hermiteMvNorm (e k) := by
    rw [norm_smul, norm_hermiteMvLp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hermiteMvNorm_pos (e k))]
  have hsc : ((hermiteMvNorm (e k) : ℝ) : ℂ)⁻¹ * ((hermiteMvNorm (e k) : ℝ) : ℂ) = 1 :=
    inv_mul_cancel₀ (hermiteMvNorm_ne_zero (e k))
  calc ((‖((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k)‖ : ℝ) : ℂ)⁻¹
        • (((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k))
      = ((hermiteMvNorm (e k) : ℝ) : ℂ)⁻¹
        • (((hermiteMvNorm (e k) : ℝ) : ℂ) • hermiteMvLp (e k)) := by
        rw [hnorm]
    _ = (((hermiteMvNorm (e k) : ℝ) : ℂ)⁻¹ * ((hermiteMvNorm (e k) : ℝ) : ℂ))
        • hermiteMvLp (e k) := smul_smul _ _ _
    _ = (1 : ℂ) • hermiteMvLp (e k) :=
        congrArg (fun x : ℂ => x • hermiteMvLp (e k)) hsc
    _ = hermiteMvLp (e k) := one_smul _ _

/-- Consequently the bridge hypothesis holds with all phases equal to `1`. -/
theorem exists_unit_phase_coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) (hdeg : DegreeCompatible e)
    (k : ℕ) : ∃ u : ℂ, ‖u‖ = 1 ∧ coreBasis e k = u • hermBasisN e k :=
  ⟨1, by simp, by rw [coreBasis_eq_hermBasisN e hdeg k, one_smul]⟩

end

end BookProof.HermiteBridgePhases
