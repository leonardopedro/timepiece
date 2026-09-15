import Mathlib
import BookProof.ChapterNavierStokesLagrangianEsa

/-!
# The Fock space of a Fock space, and its ladder operators

The Lagrangian form of the Navier–Stokes Hamiltonian of
`BookProof.ChapterNavierStokesLagrangianEsa` is a *second* quantization: the
Eulerian field `u` is already an operator on a Fock space, and passing to the
parcel variables `X(ξ)` — one field-carrying parcel for each label `ξ` in a
continuous domain — quantizes the parcels themselves.  The state space is
therefore a Fock space **whose one-particle space is itself a Fock space**, and
the Hamiltonian is *quadratic* in the outer (parcel) creation and annihilation
operators.

This module builds that state space concretely, in the occupation-number
representation, together with both levels of ladder operators.

* `lpDiag`, `lpBasis` — a general diagonal operator with a real symbol on the
  finitely supported modes of `ℓ²(ι)`, its eigenbasis, symmetry, essential
  self-adjointness (`lpDiag_hasZeroDeficiencyOn`) and unboundedness
  (`lpDiag_not_bounded`).
* `Conf M = M →₀ ℕ`, `FockL2 M = ℓ²(Conf M)`, `FockDom M` — the Fock space over
  the mode index `M` in the occupation-number representation and its dense
  domain of finite-particle, finite-mode states.
* `annih m`, `creat m` — the annihilation and creation operators, with
  `annih_basis`, `creat_basis` (the usual `√n` factors), `creat_adjoint`
  (`⟪a†v, w⟫ = ⟪v, a w⟫`) and the canonical commutation relations
  `ccr_same`, `ccr_ne`.
* `numberOp m = a†ₘ aₘ` and `numberOp_basis` — the mode occupation operator.
* `FockOfFockL2 J K = FockL2 (J × Conf K)` — **the Fock space of a Fock space**:
  the outer one-particle modes are indexed by a parcel mode `j : J` *together
  with* an inner Fock (occupation) state `c : Conf K`.  `outerOneParticle` shows
  that the outer creation operator applied to the vacuum creates exactly one
  parcel carrying the inner Fock state `c`.

The Hamiltonian itself, its integral over the continuous parcel domain and its
essential self-adjointness are in `BookProof.ChapterNavierStokesFockEsa`.
-/

namespace BookProof.NavierStokesFlow

namespace FockOfFock

open FullEsa

/-! ## Finitely supported coefficient vectors in `ℓ²(ι)` -/

section Coeff

variable {ι : Type*}

/-- A finitely supported coefficient function is square-summable. -/
theorem memℓpTwo_of_finite_support {φ : ι → ℂ} (h : (Function.support φ).Finite) :
    Memℓp φ 2 := by
  apply memℓp_gen
  refine summable_of_finite_support (Set.Finite.subset h ?_)
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by simp [hz])

/-- The finite-mode vector of `ℓ²(ι)` with the given finitely supported
coefficients. -/
def ofCoeff (φ : ι → ℂ) (h : (Function.support φ).Finite) : lpFiniteModes ι :=
  ⟨⟨φ, memℓpTwo_of_finite_support h⟩, h⟩

@[simp] theorem ofCoeff_coe (φ : ι → ℂ) (h : (Function.support φ).Finite) :
    (((ofCoeff φ h : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) = φ := rfl

/-- A coefficientwise linear operator on the finite-mode domain of `ℓ²(ι)`. -/
def coeffOp (T : (ι → ℂ) → ι → ℂ)
    (hsupp : ∀ {φ : ι → ℂ}, (Function.support φ).Finite → (Function.support (T φ)).Finite)
    (hadd : ∀ φ ψ : ι → ℂ, T (φ + ψ) = T φ + T ψ)
    (hsmul : ∀ (c : ℂ) (φ : ι → ℂ), T (c • φ) = c • T φ) :
    lpFiniteModes ι →ₗ[ℂ] lpFiniteModes ι where
  toFun f := ofCoeff (T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ)) (hsupp f.2)
  map_add' f g := by
    ext i
    have : (((f + g : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
        = ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) + ((g : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := by
      ext j; simp
    simp [ofCoeff, hadd]
  map_smul' c f := by
    ext i
    have : (((c • f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
        = c • ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := by
      ext j; simp
    simp [ofCoeff, hsmul]

@[simp] theorem coeffOp_coe (T : (ι → ℂ) → ι → ℂ) (hsupp) (hadd) (hsmul) (f : lpFiniteModes ι) :
    (((coeffOp T hsupp hadd hsmul f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
      = T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := rfl

/-- The canonical basis state `e_i` of the finite-mode domain. -/
noncomputable def lpBasis [DecidableEq ι] (i : ι) : lpFiniteModes ι :=
  ⟨lp.single 2 i 1, lpSingle_mem_lpFiniteModes i 1⟩

theorem lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]

theorem norm_lpBasis [DecidableEq ι] (i : ι) : ‖lpBasis (ι := ι) i‖ = 1 := by
  have : ‖((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2)‖ = ‖(1 : ℂ)‖ :=
    lp.norm_single (by norm_num) i 1
  simpa using this

/-- The basis states are total: only `0` is orthogonal to all of them. -/
theorem lpBasis_total [DecidableEq ι] (w : lp (fun _ : ι => ℂ) 2)
    (hw : ∀ i, (inner ℂ ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) w : ℂ) = 0) :
    w = 0 := by
  ext i
  have h := hw i
  rw [show ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) = lp.single 2 i 1 from rfl,
    lp.inner_single_left] at h
  simpa using h

/-- **For an infinite mode index the finite-mode domain is a proper subspace**:
the `ℓ²` state supported on an infinite family of modes with coefficients
`1/(k+1)` has infinitely many excited modes.  So statements of essential
self-adjointness on this domain are genuine (non-`⊤`) ones. -/
theorem lpFiniteModes_ne_top (ι : Type*) [Infinite ι] :
    lpFiniteModes ι ≠ (⊤ : Submodule ℂ (lp (fun _ : ι => ℂ) 2)) := by
  classical
  set e : ℕ ↪ ι := Infinite.natEmbedding ι with he
  set φ : ι → ℂ := fun i => if h : ∃ k, e k = i then 1 / ((Classical.choose h : ℕ) + 1 : ℂ) else 0
    with hφ
  have hval : ∀ k : ℕ, φ (e k) = 1 / ((k : ℂ) + 1) := by
    intro k
    have hex : ∃ j, e j = e k := ⟨k, rfl⟩
    have hchoose : Classical.choose hex = k := e.injective (Classical.choose_spec hex)
    simp only [hφ, dif_pos hex, hchoose]
  have hout : ∀ i ∉ Set.range e, ‖φ i‖ ^ 2 = 0 := by
    intro i hi
    have : ¬ ∃ k, e k = i := fun ⟨k, hk⟩ => hi ⟨k, hk⟩
    simp [hφ, dif_neg this]
  have hsummable : Summable fun i => ‖φ i‖ ^ 2 := by
    refine (e.injective.summable_iff hout).1 ?_
    have hcomp : (fun k : ℕ => ‖φ (e k)‖ ^ 2) = fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2 := by
      funext k
      have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hval k, hcast, norm_div, norm_one, Complex.norm_natCast]
      push_cast
      ring
    have hsum : Summable fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2 := by
      have hbase := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      refine ((summable_nat_add_iff 1).2 hbase).congr fun k => ?_
      push_cast
      rw [div_pow, one_pow]
    rw [Function.comp_def, hcomp]
    exact hsum
  have hmem : Memℓp φ 2 := by
    apply memℓp_gen
    simpa using hsummable
  intro htop
  have hg : (⟨φ, hmem⟩ : lp (fun _ : ι => ℂ) 2) ∈ lpFiniteModes ι := htop ▸ Submodule.mem_top
  rw [mem_lpFiniteModes] at hg
  have hsub : Set.range e ⊆ Function.support φ := by
    rintro _ ⟨k, rfl⟩
    have : φ (e k) ≠ 0 := by
      rw [hval k]
      refine one_div_ne_zero ?_
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]
      exact_mod_cast Nat.succ_ne_zero k
    simpa [Function.mem_support] using this
  exact (Set.infinite_range_of_injective e.injective) (hg.subset hsub)

end Coeff

/-! ## Diagonal operators with a real symbol -/

section Diagonal

variable {ι : Type*}

/-- Coefficientwise multiplication by a real symbol. -/
def diagCoeff (c : ι → ℝ) (φ : ι → ℂ) : ι → ℂ := fun i => (c i : ℂ) * φ i

/-- The diagonal operator with real symbol `c` on the finite-mode domain of
`ℓ²(ι)`.  For an unbounded symbol it is an unbounded operator. -/
noncomputable def lpDiag (c : ι → ℝ) : lpFiniteModes ι →ₗ[ℂ] lpFiniteModes ι :=
  coeffOp (diagCoeff c)
    (fun {φ} h => h.subset (by
      intro i hi
      simp only [Function.mem_support, diagCoeff] at hi ⊢
      intro hz
      exact hi (by simp [hz])))
    (fun φ ψ => by funext i; simp [diagCoeff]; ring)
    (fun a φ => by funext i; simp [diagCoeff]; ring)

@[simp] theorem lpDiag_coe (c : ι → ℝ) (f : lpFiniteModes ι) (i : ι) :
    (((lpDiag c f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
      = (c i : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i := rfl

theorem lpDiag_basis [DecidableEq ι] (c : ι → ℝ) (i : ι) :
    lpDiag c (lpBasis i) = ((c i : ℝ) : ℂ) • lpBasis i := by
  ext j
  by_cases h : j = i
  · subst h; simp [lpDiag_coe, lpBasis_coe]
  · simp [lpDiag_coe, lpBasis_coe, h]

theorem lpDiag_isSymmetricDom (c : ι → ℝ) : IsSymmetricDom (lpDiag c) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [RCLike.inner_apply, lpDiag_coe, map_mul, Complex.conj_ofReal]
  ring

/-- **A diagonal operator with an arbitrary real symbol is essentially
self-adjoint** on the finite-mode domain: its basis states are a total family of
eigenvectors with real eigenvalues.  No boundedness is required. -/
theorem lpDiag_hasZeroDeficiencyOn (c : ι → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ι) (lpDiag c) := by
  classical
  exact hasZeroDeficiencyOn_of_total_eigenvectors _ _ lpBasis c (lpDiag_basis c) lpBasis_total

/-- The diagonal operator is genuinely unbounded when its symbol is. -/
theorem lpDiag_not_bounded (c : ι → ℝ) (hc : ∀ C : ℝ, ∃ i, C < |c i|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ι, ‖lpDiag c f‖ ≤ C * ‖f‖ := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨i, hi⟩ := hc C
  have hb := hC (lpBasis i)
  rw [lpDiag_basis, norm_smul, norm_lpBasis] at hb
  have hle : |c i| ≤ C := by simpa using hb
  exact absurd hi (not_lt.mpr hle)

end Diagonal

end FockOfFock

end BookProof.NavierStokesFlow
