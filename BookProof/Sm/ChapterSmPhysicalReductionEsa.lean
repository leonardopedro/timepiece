/-
Copyright (c) 2026 Leopoldo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leopoldo
-/
import BookProof.Sm.ChapterSmFullMatterHamiltonian

/-!
# P5: the parity reduction of the closed coupled inner operator

`BookProof.SmFullMatter` proves that `coupledParity` is a norm-preserving involution of
the coupled space, that it preserves the common core `SmCoupledCore`, and that it
commutes with the full normal form on that core (`smNormalForm_parity`).  The plan
records (`SM_ESA_COMPLETION_PLAN.md`, P5) that this is a **core-level** identity: "the
closure's graph has no commutation statement, so the strong reduction is not obtained".

This module supplies that statement.  Deficiency spaces — the corpus's representation of
the closure (`BookProof.FarisLavine.DeficiencyTrivialAt`) — are split by parity:

* `deficiencyTrivialAt_iff_sectors` : for a unitary involution `U`, an invariant core `D`
  and a core operator `T` commuting with `U` on `D`, the deficiency space of `T` at `z`
  is trivial iff both sector deficiency problems are trivial.  The proof extends a sector
  deficiency to the whole core by splitting `v = ½(v+Uv) + ½(v−Uv)` and using
  orthogonality of the sectors, so it is a statement about the closed operator.
* `smNormalForm_esd_iff_parity_sectors` : the SM instance, with no hypothesis beyond
  `HermitianCoeffs` and `ParityGradedCoeffs`.
* `sectorCore_topologicalClosure` : each sector core is dense in its sector.

## What is *not* claimed

Essential self-adjointness of the sector operators themselves is P4's elliptic input
(`PotSelfBound` / `FormDomainComparison`) and stays a hypothesis.  The gauge (BRST)
sector and the graded outer lift `Γ_s ⊗ Γ_a` are not built here; the lift consumes the
sector essential self-adjointness, so it remains conditional on the same P4 input.
-/

namespace BookProof.SmPhysicalReduction

open BookProof.FarisLavine

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. The two parts of an involution -/

/-- The even part `½(x + Ux)` of a vector. -/
def evenPart (U : H →ₗ[ℂ] H) (x : H) : H := (2⁻¹ : ℂ) • (x + U x)

/-- The odd part `½(x − Ux)` of a vector. -/
def oddPart (U : H →ₗ[ℂ] H) (x : H) : H := (2⁻¹ : ℂ) • (x - U x)

/-- The even sector `ker (U − 1)`. -/
def evenSpace (U : H →ₗ[ℂ] H) : Submodule ℂ H := LinearMap.ker (U - LinearMap.id)

/-- The odd sector `ker (U + 1)`. -/
def oddSpace (U : H →ₗ[ℂ] H) : Submodule ℂ H := LinearMap.ker (U + LinearMap.id)

variable {U : H →ₗ[ℂ] H}

theorem mem_evenSpace_iff (x : H) : x ∈ evenSpace U ↔ U x = x := by
  rw [evenSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_oddSpace_iff (x : H) : x ∈ oddSpace U ↔ U x = -x := by
  rw [oddSpace, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg]

theorem U_apply_U (hU : U ∘ₗ U = LinearMap.id) (x : H) : U (U x) = x :=
  congrFun (congrArg DFunLike.coe hU) x

theorem evenPart_add_oddPart (x : H) : evenPart U x + oddPart U x = x := by
  have hsum : (x + U x) + (x - U x) = (2 : ℂ) • x := by
    rw [two_smul]
    abel
  rw [evenPart, oddPart, ← smul_add, hsum, smul_smul]
  norm_num

theorem evenPart_mem (hU : U ∘ₗ U = LinearMap.id) (x : H) : evenPart U x ∈ evenSpace U := by
  rw [mem_evenSpace_iff, evenPart, map_smul, map_add, U_apply_U hU, add_comm (U x) x]

theorem oddPart_mem (hU : U ∘ₗ U = LinearMap.id) (x : H) : oddPart U x ∈ oddSpace U := by
  rw [mem_oddSpace_iff, oddPart, map_smul, map_sub, U_apply_U hU, ← smul_neg, neg_sub]

/-! ## 2. Unitarity: the sectors are orthogonal -/

/-- A norm-preserving linear map preserves the inner product. -/
theorem inner_map_map_of_norm_map (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (x y : H) :
    inner ℂ (U x) (U y) = inner ℂ x y :=
  ({ toLinearMap := U, norm_map' := hUnorm } : H →ₗᵢ[ℂ] H).inner_map_map x y

/-- A unitary involution is self-adjoint. -/
theorem inner_map_left_eq (hU : U ∘ₗ U = LinearMap.id)
    (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (x y : H) :
    inner ℂ (U x) y = inner ℂ x (U y) := by
  rw [← inner_map_map_of_norm_map (U := U) hUnorm x (U y), U_apply_U hU]

/-- **The even and odd sectors of a unitary involution are orthogonal.** -/
theorem inner_eq_zero_of_mem_even_of_mem_odd (hU : U ∘ₗ U = LinearMap.id)
    (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) {a b : H}
    (ha : a ∈ evenSpace U) (hb : b ∈ oddSpace U) : inner ℂ a b = 0 := by
  have hUa : U a = a := (mem_evenSpace_iff a).mp ha
  have hUb : U b = -b := (mem_oddSpace_iff b).mp hb
  have hkey : inner ℂ (U a) b = inner ℂ a (U b) := inner_map_left_eq hU hUnorm a b
  rw [hUa, hUb, inner_neg_right] at hkey
  have h2 : inner ℂ a b + inner ℂ a b = 0 := by linear_combination hkey
  have hzero : inner ℂ a b * 2 = 0 := by rw [mul_two]; exact h2
  exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)

/-- The same orthogonality with the odd vector first. -/
theorem inner_eq_zero_of_mem_odd_of_mem_even (hU : U ∘ₗ U = LinearMap.id)
    (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) {a b : H}
    (ha : a ∈ oddSpace U) (hb : b ∈ evenSpace U) : inner ℂ a b = 0 := by
  rw [← inner_conj_symm, inner_eq_zero_of_mem_even_of_mem_odd hU hUnorm hb ha, map_zero]

/-! ## 3. The sector reduction of a symmetric operator on an invariant core -/

/-- The even part of the core. -/
def evenCore (U : H →ₗ[ℂ] H) (D : Submodule ℂ H) : Submodule ℂ H := D ⊓ evenSpace U

/-- The odd part of the core. -/
def oddCore (U : H →ₗ[ℂ] H) (D : Submodule ℂ H) : Submodule ℂ H := D ⊓ oddSpace U

theorem evenPart_mem_of_mem {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) {x : H} (hx : x ∈ D) : evenPart U x ∈ D := by
  rw [evenPart, smul_add]
  exact D.add_mem (D.smul_mem _ hx) (D.smul_mem _ (hDU x hx))

theorem oddPart_mem_of_mem {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) {x : H} (hx : x ∈ D) : oddPart U x ∈ D := by
  rw [oddPart, smul_sub]
  exact D.sub_mem (D.smul_mem _ hx) (D.smul_mem _ (hDU x hx))

theorem evenPart_mem_core {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (hU : U ∘ₗ U = LinearMap.id) {x : H} (hx : x ∈ D) :
    evenPart U x ∈ evenCore U D :=
  ⟨evenPart_mem_of_mem D hDU hx, evenPart_mem hU x⟩

theorem oddPart_mem_core {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (hU : U ∘ₗ U = LinearMap.id) {x : H} (hx : x ∈ D) :
    oddPart U x ∈ oddCore U D :=
  ⟨oddPart_mem_of_mem D hDU hx, oddPart_mem hU x⟩

/-- The restriction of `T` to the even part of the core. -/
def evenOp (U : H →ₗ[ℂ] H) (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : evenCore U D →ₗ[ℂ] H where
  toFun x := T ⟨(x : H), x.2.1⟩
  map_add' x y := by
    have h : (⟨((x : H) + (y : H)), D.add_mem x.2.1 y.2.1⟩ : D)
        = (⟨(x : H), x.2.1⟩ : D) + ⟨(y : H), y.2.1⟩ := Subtype.ext rfl
    change T ⟨((x : H) + (y : H)), D.add_mem x.2.1 y.2.1⟩
        = T ⟨(x : H), x.2.1⟩ + T ⟨(y : H), y.2.1⟩
    rw [h, map_add]
  map_smul' c x := by
    have h : (⟨c • (x : H), D.smul_mem c x.2.1⟩ : D) = c • (⟨(x : H), x.2.1⟩ : D) :=
      Subtype.ext rfl
    change T ⟨c • (x : H), D.smul_mem c x.2.1⟩ = c • T ⟨(x : H), x.2.1⟩
    rw [h, map_smul]

/-- The restriction of `T` to the odd part of the core. -/
def oddOp (U : H →ₗ[ℂ] H) (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : oddCore U D →ₗ[ℂ] H where
  toFun x := T ⟨(x : H), x.2.1⟩
  map_add' x y := by
    have h : (⟨((x : H) + (y : H)), D.add_mem x.2.1 y.2.1⟩ : D)
        = (⟨(x : H), x.2.1⟩ : D) + ⟨(y : H), y.2.1⟩ := Subtype.ext rfl
    change T ⟨((x : H) + (y : H)), D.add_mem x.2.1 y.2.1⟩
        = T ⟨(x : H), x.2.1⟩ + T ⟨(y : H), y.2.1⟩
    rw [h, map_add]
  map_smul' c x := by
    have h : (⟨c • (x : H), D.smul_mem c x.2.1⟩ : D) = c • (⟨(x : H), x.2.1⟩ : D) :=
      Subtype.ext rfl
    change T ⟨c • (x : H), D.smul_mem c x.2.1⟩ = c • T ⟨(x : H), x.2.1⟩
    rw [h, map_smul]

theorem evenOp_apply {U : H →ₗ[ℂ] H} {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (x : evenCore U D) : evenOp U D T x = T ⟨(x : H), x.2.1⟩ := rfl

theorem oddOp_apply {U : H →ₗ[ℂ] H} {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (x : oddCore U D) : oddOp U D T x = T ⟨(x : H), x.2.1⟩ := rfl

/-- The even restriction lands in the even sector. -/
theorem evenOp_mem {U : H →ₗ[ℂ] H} (D : Submodule ℂ H) (hDU : ∀ x ∈ D, U x ∈ D)
    (T : D →ₗ[ℂ] H) (hTU : ∀ x : D, T ⟨U x, hDU _ x.2⟩ = U (T x))
    (x : evenCore U D) : evenOp U D T x ∈ evenSpace U := by
  have hx : U (x : H) = (x : H) := (mem_evenSpace_iff _).mp x.2.2
  have h2 : (⟨U (x : H), hDU _ x.2.1⟩ : D) = ⟨(x : H), x.2.1⟩ := Subtype.ext hx
  have h := hTU ⟨(x : H), x.2.1⟩
  rw [h2] at h
  rw [evenOp_apply, mem_evenSpace_iff]
  exact h.symm

/-- The odd restriction lands in the odd sector. -/
theorem oddOp_mem {U : H →ₗ[ℂ] H} (D : Submodule ℂ H) (hDU : ∀ x ∈ D, U x ∈ D)
    (T : D →ₗ[ℂ] H) (hTU : ∀ x : D, T ⟨U x, hDU _ x.2⟩ = U (T x))
    (x : oddCore U D) : oddOp U D T x ∈ oddSpace U := by
  have hx : U (x : H) = -(x : H) := (mem_oddSpace_iff _).mp x.2.2
  have h2 : (⟨U (x : H), hDU _ x.2.1⟩ : D) = (-⟨(x : H), x.2.1⟩ : D) := Subtype.ext hx
  have h := hTU ⟨(x : H), x.2.1⟩
  rw [h2, map_neg] at h
  rw [oddOp_apply, mem_oddSpace_iff]
  exact h.symm

/-- **Sector deficiency**: the analogue of `DeficiencyTrivialAt` for one parity sector.
The test vector `w` is required to lie in the sector. -/
def SectorDeficiencyTrivial {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ds : Submodule ℂ H) (Ts : Ds →ₗ[ℂ] H) (P : Submodule ℂ H) (z : ℂ) : Prop :=
  ∀ w ∈ P, (∀ v : Ds, inner ℂ (Ts v) w = z * inner ℂ (v : H) w) → w = 0

/-- **The even extension step.**  A vector of the even sector that solves the deficiency
equation against the even part of the core solves it against the whole core. -/
theorem deficiency_at_of_even_deficiency {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (T : D →ₗ[ℂ] H)
    (hTU : ∀ x : D, T ⟨U x, hDU _ x.2⟩ = U (T x))
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) {z : ℂ} {w : H}
    (hw : w ∈ evenSpace U)
    (hsector : ∀ v : evenCore U D, inner ℂ (evenOp U D T v) w = z * inner ℂ (v : H) w) :
    ∀ v : D, inner ℂ (T v) w = z * inner ℂ (v : H) w := by
  intro v
  set e : H := evenPart U (v : H) with he
  set o : H := oddPart U (v : H) with ho
  have heD : e ∈ D := he.symm ▸ evenPart_mem_of_mem D hDU v.2
  have hoD : o ∈ D := ho.symm ▸ oddPart_mem_of_mem D hDU v.2
  have heE : e ∈ evenSpace U := he.symm ▸ evenPart_mem hU (v : H)
  have hoO : o ∈ oddSpace U := ho.symm ▸ oddPart_mem hU (v : H)
  have hv : v = (⟨e, heD⟩ : D) + ⟨o, hoD⟩ := by
    refine Subtype.ext ?_
    change (v : H) = e + o
    rw [he, ho]
    exact (evenPart_add_oddPart (v : H)).symm
  have hTo : T ⟨o, hoD⟩ ∈ oddSpace U := by
    have h2 : (⟨U o, hDU _ hoD⟩ : D) = (-⟨o, hoD⟩ : D) :=
      Subtype.ext ((mem_oddSpace_iff _).mp hoO)
    have h := hTU ⟨o, hoD⟩
    simp only [h2, map_neg] at h
    rw [mem_oddSpace_iff]
    exact h.symm
  have horth : inner ℂ (T ⟨o, hoD⟩) w = 0 :=
    inner_eq_zero_of_mem_odd_of_mem_even hU hUnorm hTo hw
  have horthv : inner ℂ o w = 0 :=
    inner_eq_zero_of_mem_odd_of_mem_even hU hUnorm hoO hw
  have hsum : ((⟨e, ⟨heD, heE⟩⟩ : evenCore U D) : H) + ((⟨o, hoD⟩ : D) : H) = (v : H) := by
    change e + o = (v : H)
    rw [he, ho]
    exact evenPart_add_oddPart (v : H)
  calc inner ℂ (T v) w
      = inner ℂ (T ((⟨e, heD⟩ : D) + ⟨o, hoD⟩)) w := by rw [hv]
    _ = inner ℂ (T ⟨e, heD⟩ + T ⟨o, hoD⟩) w := by rw [map_add]
    _ = inner ℂ (T ⟨e, heD⟩) w + inner ℂ (T ⟨o, hoD⟩) w := by rw [inner_add_left]
    _ = inner ℂ (T ⟨e, heD⟩) w := by rw [horth, add_zero]
    _ = inner ℂ (evenOp U D T ⟨e, ⟨heD, heE⟩⟩) w := by rw [evenOp_apply]
    _ = z * inner ℂ (((⟨e, ⟨heD, heE⟩⟩ : evenCore U D)) : H) w := hsector _
    _ = z * inner ℂ (v : H) w := by rw [← hsum, inner_add_left, horthv, add_zero]

/-- **The odd extension step** — the same statement in the odd sector. -/
theorem deficiency_at_of_odd_deficiency {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (T : D →ₗ[ℂ] H)
    (hTU : ∀ x : D, T ⟨U x, hDU _ x.2⟩ = U (T x))
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) {z : ℂ} {w : H}
    (hw : w ∈ oddSpace U)
    (hsector : ∀ v : oddCore U D, inner ℂ (oddOp U D T v) w = z * inner ℂ (v : H) w) :
    ∀ v : D, inner ℂ (T v) w = z * inner ℂ (v : H) w := by
  intro v
  set e : H := evenPart U (v : H) with he
  set o : H := oddPart U (v : H) with ho
  have heD : e ∈ D := he.symm ▸ evenPart_mem_of_mem D hDU v.2
  have hoD : o ∈ D := ho.symm ▸ oddPart_mem_of_mem D hDU v.2
  have heE : e ∈ evenSpace U := he.symm ▸ evenPart_mem hU (v : H)
  have hoO : o ∈ oddSpace U := ho.symm ▸ oddPart_mem hU (v : H)
  have hv : v = (⟨e, heD⟩ : D) + ⟨o, hoD⟩ := by
    refine Subtype.ext ?_
    change (v : H) = e + o
    rw [he, ho]
    exact (evenPart_add_oddPart (v : H)).symm
  have hTe : T ⟨e, heD⟩ ∈ evenSpace U := by
    have h2 : (⟨U e, hDU _ heD⟩ : D) = ⟨e, heD⟩ :=
      Subtype.ext ((mem_evenSpace_iff _).mp heE)
    have h := hTU ⟨e, heD⟩
    simp only [h2] at h
    rw [mem_evenSpace_iff]
    exact h.symm
  have horth : inner ℂ (T ⟨e, heD⟩) w = 0 :=
    inner_eq_zero_of_mem_even_of_mem_odd hU hUnorm hTe hw
  have horthv : inner ℂ e w = 0 :=
    inner_eq_zero_of_mem_even_of_mem_odd hU hUnorm heE hw
  have hsum : ((⟨e, heD⟩ : D) : H) + ((⟨o, ⟨hoD, hoO⟩⟩ : oddCore U D) : H) = (v : H) := by
    change e + o = (v : H)
    rw [he, ho]
    exact evenPart_add_oddPart (v : H)
  calc inner ℂ (T v) w
      = inner ℂ (T ((⟨e, heD⟩ : D) + ⟨o, hoD⟩)) w := by rw [hv]
    _ = inner ℂ (T ⟨e, heD⟩ + T ⟨o, hoD⟩) w := by rw [map_add]
    _ = inner ℂ (T ⟨e, heD⟩) w + inner ℂ (T ⟨o, hoD⟩) w := by rw [inner_add_left]
    _ = inner ℂ (T ⟨o, hoD⟩) w := by rw [horth, zero_add]
    _ = inner ℂ (oddOp U D T ⟨o, ⟨hoD, hoO⟩⟩) w := by rw [oddOp_apply]
    _ = z * inner ℂ (((⟨o, ⟨hoD, hoO⟩⟩ : oddCore U D)) : H) w := hsector _
    _ = z * inner ℂ (v : H) w := by rw [← hsum, inner_add_left, horthv, zero_add]

/-- **The reduction of the deficiency space, hence of the closure.** -/
theorem deficiencyTrivialAt_iff_sectors {U : H →ₗ[ℂ] H} (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (T : D →ₗ[ℂ] H)
    (hTU : ∀ x : D, T ⟨U x, hDU _ x.2⟩ = U (T x))
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (z : ℂ) :
    DeficiencyTrivialAt D T z ↔
      SectorDeficiencyTrivial (evenCore U D) (evenOp U D T) (evenSpace U) z ∧
      SectorDeficiencyTrivial (oddCore U D) (oddOp U D T) (oddSpace U) z := by
  constructor
  · intro hD
    refine ⟨?_, ?_⟩
    · intro w hw hsector
      exact hD w (deficiency_at_of_even_deficiency D hDU T hTU hU hUnorm hw hsector)
    · intro w hw hsector
      exact hD w (deficiency_at_of_odd_deficiency D hDU T hTU hU hUnorm hw hsector)
  · rintro ⟨heven, hodd⟩ w hw
    have hUw : ∀ v : D, inner ℂ (T v) (U w) = z * inner ℂ (v : H) (U w) := by
      intro v
      have h := hw ⟨U (v : H), hDU _ v.2⟩
      rw [hTU ⟨(v : H), v.2⟩, inner_map_left_eq hU hUnorm,
        inner_map_left_eq hU hUnorm] at h
      exact h
    have hlin : ∀ c d : ℂ,
        (∀ v : D, inner ℂ (T v) w = z * inner ℂ (v : H) w) →
        (∀ v : D, inner ℂ (T v) (U w) = z * inner ℂ (v : H) (U w)) →
        ∀ v : D,
          inner ℂ (T v) (c • w + d • U w) = z * inner ℂ (v : H) (c • w + d • U w) := by
      intro c d hw' hUw' v
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, inner_smul_right, hw' v, hUw' v]
      ring
    have hweven : evenPart U w = 0 := by
      refine heven (evenPart U w) (evenPart_mem hU w) ?_
      intro v
      have h := hlin (2⁻¹ : ℂ) (2⁻¹ : ℂ) hw hUw ⟨(v : H), v.2.1⟩
      simpa only [evenPart, smul_add, evenOp_apply] using h
    have hwodd : oddPart U w = 0 := by
      refine hodd (oddPart U w) (oddPart_mem hU w) ?_
      intro v
      have hsplit : oddPart U w = (2⁻¹ : ℂ) • w + (-(2⁻¹ : ℂ)) • U w := by
        rw [oddPart, smul_sub, sub_eq_add_neg, neg_smul]
      rw [show (oddOp U D T) v = T ⟨(v : H), v.2.1⟩ from oddOp_apply v, hsplit]
      exact hlin (2⁻¹ : ℂ) (-(2⁻¹ : ℂ)) hw hUw ⟨(v : H), v.2.1⟩
    calc w = evenPart U w + oddPart U w := (evenPart_add_oddPart w).symm
      _ = 0 := by rw [hweven, hwodd, add_zero]

/-! ## 4. The SM instance

The plan's P5 records that `smNormalForm_parity` is a *core-level* identity, so it does not by
itself reduce the closure.  `deficiencyTrivialAt_iff_sectors` closes exactly that gap; here it is
instantiated at the full matter normal form.  Parity is a norm-preserving involution
(`coupledParity_involutive`, `coupledParity_norm`), it preserves the common core
(`coupledParity_mem_core`), and it commutes with the normal form on that core
(`smNormalForm_parity`), so all the hypotheses of the reduction are discharged by existing
theorems and no new analytic input is introduced.
-/

section SmInstance

open BookProof.SmFullMatter

/-- Parity preserves the inner product of the coupled space. -/
theorem coupledParity_inner (f g : SmCoupledSpace) :
    inner ℂ (coupledParity f) (coupledParity g) = inner ℂ f g :=
  ({ toLinearMap := coupledParity, norm_map' := coupledParity_norm } :
    SmCoupledSpace →ₗᵢ[ℂ] SmCoupledSpace).inner_map_map f g

/-- **Parity commutes with the normal form on the common core**, in the orientation the sector
reduction consumes. -/
theorem smNormalForm_parity_core (D : SmNormalFormData) (hD : ParityGradedCoeffs D)
    (x : SmCoupledCore) :
    smNormalForm D ⟨coupledParity (x : SmCoupledSpace), coupledParity_mem_core _ x.2⟩
      = coupledParity (smNormalForm D x) := by
  have hx : (⟨coupledParity (x : SmCoupledSpace), coupledParity_mem_core _ x.2⟩ : SmCoupledCore)
      = coupledParityCore x := Subtype.ext (coe_coupledParityCore x).symm
  rw [hx]
  exact (smNormalForm_parity D hD x).symm

set_option maxRecDepth 4000 in
/-- **P5, the SM instance**: essential self-adjointness of the full matter normal form on the common
core is *equivalent* to the two decoupled parity-sector deficiency problems, one for each sign of
the deflation parameter.  No hypothesis beyond the parity grading of the coefficient data is used;
in particular the demand is not strengthened. -/
theorem smNormalForm_esd_iff_parity_sectors (D : SmNormalFormData)
    (hD : ParityGradedCoeffs D) :
    EssentiallySelfAdjointOn SmCoupledCore (smNormalForm D) ↔
      (SectorDeficiencyTrivial (evenCore coupledParity SmCoupledCore)
          (evenOp coupledParity SmCoupledCore (smNormalForm D)) (evenSpace coupledParity)
            Complex.I ∧
        SectorDeficiencyTrivial (oddCore coupledParity SmCoupledCore)
          (oddOp coupledParity SmCoupledCore (smNormalForm D)) (oddSpace coupledParity) Complex.I) ∧
      (SectorDeficiencyTrivial (evenCore coupledParity SmCoupledCore)
          (evenOp coupledParity SmCoupledCore (smNormalForm D)) (evenSpace coupledParity)
            (-Complex.I) ∧
        SectorDeficiencyTrivial (oddCore coupledParity SmCoupledCore)
          (oddOp coupledParity SmCoupledCore (smNormalForm D)) (oddSpace coupledParity)
            (-Complex.I)) := by
  have hmain (z : ℂ) := deficiencyTrivialAt_iff_sectors (U := coupledParity) SmCoupledCore
    coupledParity_mem_core (smNormalForm D) (smNormalForm_parity_core D hD)
    coupledParity_involutive coupledParity_norm z
  refine ⟨?_, ?_⟩
  · rintro ⟨hI, hni⟩
    exact ⟨(hmain Complex.I).mp hI, (hmain (-Complex.I)).mp hni⟩
  · rintro ⟨hI, hni⟩
    exact ⟨(hmain Complex.I).mpr hI, (hmain (-Complex.I)).mpr hni⟩

end SmInstance

/-! ## 5. The sector cores are dense graph cores -/

section Dense

variable {U : H →ₗ[ℂ] H}

theorem evenSpace_neg (U : H →ₗ[ℂ] H) : evenSpace (-U) = oddSpace U := by
  ext x
  simp only [mem_evenSpace_iff, mem_oddSpace_iff, LinearMap.neg_apply, neg_eq_iff_eq_neg]

/-- **The even part of a dense invariant core is dense in the even sector.**  Hence the restriction
of a core operator to the even sector has a dense graph core, as the sector reduction requires. -/
theorem topologicalClosure_evenCore (hU : U ∘ₗ U = LinearMap.id)
    (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (hDense : Dense (D : Set H)) :
    (evenCore U D).topologicalClosure = evenSpace U := by
  have hUc : Continuous (U : H → H) :=
    AddMonoidHomClass.continuous_of_bound U 1 (fun x => by
      rw [one_mul]
      exact (hUnorm x).le)
  have hec : Continuous (evenPart U) := by
    unfold evenPart
    exact continuous_const.smul (continuous_id.add hUc)
  have hclosed : IsClosed (evenSpace U : Set H) := by
    have hset : (evenSpace U : Set H) = {x : H | U x - x = 0} := by
      ext x
      show x ∈ evenSpace U ↔ U x - x = 0
      rw [mem_evenSpace_iff, sub_eq_zero]
    rw [hset]
    exact isClosed_eq (hUc.sub continuous_id) continuous_const
  refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hclosed) ?_
  · intro x hx
    exact hx.2
  · intro x hx
    have hxfix : evenPart U x = x := by
      rw [evenPart, (mem_evenSpace_iff x).mp hx, ← two_smul ℂ x, smul_smul]
      norm_num
    have hxcl : x ∈ closure (D : Set H) := by
      have htop : D.topologicalClosure = ⊤ :=
        (Submodule.dense_iff_topologicalClosure_eq_top).mp hDense
      rw [← Submodule.topologicalClosure_coe, htop]
      exact Submodule.mem_top
    have hsub : (evenPart U) '' (D : Set H) ⊆ ((evenCore U D : Submodule ℂ H) : Set H) := by
      rintro _ ⟨y, hy, rfl⟩
      exact evenPart_mem_core D hDU hU hy
    have hmem : x ∈ closure ((evenPart U) '' (D : Set H)) :=
      image_closure_subset_closure_image hec ⟨x, hxcl, hxfix⟩
    exact closure_mono hsub hmem

theorem evenCore_neg (U : H →ₗ[ℂ] H) (D : Submodule ℂ H) :
    evenCore (-U) D = oddCore U D := by
  ext x
  simp [evenCore, oddCore, evenSpace_neg]

/-- **The odd part of a dense invariant core is dense in the odd sector.** -/
theorem topologicalClosure_oddCore (hU : U ∘ₗ U = LinearMap.id)
    (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (D : Submodule ℂ H)
    (hDU : ∀ x ∈ D, U x ∈ D) (hDense : Dense (D : Set H)) :
    (oddCore U D).topologicalClosure = oddSpace U := by
  have hneg : (-U) ∘ₗ (-U) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, map_neg,
      neg_neg]
    exact U_apply_U hU x
  have hUnorm' : ∀ x : H, ‖(-U) x‖ = ‖x‖ := fun x => by simpa using hUnorm x
  have hDU' : ∀ x ∈ D, (-U) x ∈ D := fun x hx => by
    simpa using D.neg_mem (hDU x hx)
  have h := topologicalClosure_evenCore hneg hUnorm' D hDU' hDense
  rw [evenCore_neg, evenSpace_neg] at h
  exact h

end Dense

end

end BookProof.SmPhysicalReduction
