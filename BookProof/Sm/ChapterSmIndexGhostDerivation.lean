/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The b-ghost of the derivation form of `smBrstCharge`

Section §60 of `SM_ESA_COMPLETION_PLAN.md` recorded the obstruction to identifying the
index-restricted ghost quartet (§57) with the Standard Model charge: `smBrstCharge` is a
*derivation*,

  `Ω = ∑_a χ_a G^a − ½ ∑_{a,b,c} f_{abc} χ_a χ_b β_c`,

so it does not preserve the one-particle ghost sector, and "the b-ghost of the derivation" was left
open.  This file closes that object down: the b-ghost is the **antighost sum**

  `b = ∑_a β_a`,

and its anticommutator with the derivation's matter half is the Gauss-law generator `∑_a G^a`,
not the identity:

  `{∑_a χ_a G^a, ∑_b β_b} = ∑_a G^a`.

So `b` is a contracting homotopy for `∑ χ_a G^a` exactly when the gauge generators sum to the
identity, which they cannot: the contraction has nowhere to land but the matter sector.  Two
consequences are recorded:

* `bGhost_anticomm_abelian` — when the gauge generators sum to zero the anticommutator vanishes,
  and the index quartet of §57 is that fibre;
* `bGhost_no_contraction` — the antighost's anticommutator with the matter half is `1` only if the
  gauge generators themselves sum to `1`.

The structure-constant half `−½ ∑ f_{abc} χ_a χ_b β_c` is *not* covered here; its anticommutator
with `b` is a ghost–antighost bilinear carrying `f`, which is why the free ghost complex is not a
subcomplex of the interacting one.  That remainder is described in §62.3 of the plan and is not
formalized.
-/

import BookProof.Sm.ChapterSmBrstGhost

namespace BookProof.SmIndexGhostDerivation

open BookProof.SmBrstGhost BookProof.SmCar

/-- The matter half of the derivation, `∑_a χ_a G^a`. -/
noncomputable def matterHalf (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) :
    Module.End ℂ (FermiFock (m + 12)) :=
  ∑ a : Fin 12, ghostCre m a * matterGen m T a

/-- **The b-ghost of the derivation**: the antighost sum `∑_a β_a`.  In the Fock space the
antighost is the adjoint of the ghost (`ghost_pairing` in `ChapterSmIndexGhostFock`), so this is the
same object the quartet's `P` is built from. -/
noncomputable def bGhost (m : ℕ) : Module.End ℂ (FermiFock (m + 12)) :=
  ∑ b : Fin 12, ghostAnn m b

/-- The Gauss-law generator: the sum of the constraint operators. -/
noncomputable def gaussSum (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) :
    Module.End ℂ (FermiFock (m + 12)) :=
  ∑ a : Fin 12, matterGen m T a

/-- The per-pair identity: one ghost–matter term contracted with one antighost gives the Gauss
generator on the diagonal and nothing off it. -/
theorem pair_anticomm (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a b : Fin 12) :
    ghostCre m a * matterGen m T a * ghostAnn m b
        + ghostAnn m b * (ghostCre m a * matterGen m T a)
      = if a = b then matterGen m T a else 0 := by
  have hcomm := matterGen_comm_ghostAnn m T a b
  have hcar := (smGhostCAR m).betachi b a
  rw [mul_assoc, hcomm, ← mul_assoc, ← mul_assoc (ghostAnn m b), ← add_mul,
    add_comm (ghostCre m a * ghostAnn m b), hcar]
  by_cases hab : b = a
  · rw [if_pos hab, one_mul, if_pos hab.symm]
  · rw [if_neg hab, zero_mul, if_neg (Ne.symm hab)]

/-- **The anticommutator of the b-ghost with the derivation's matter half is the Gauss generator.**
`G^a` commutes with the antighosts, so the two orderings of `χ_a G^a β_b` combine into
`{χ_a, β_b} G^a = δ_{ab} G^a`, and the sum over `b` collapses. -/
theorem bGhost_anticomm (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) :
    matterHalf m T * bGhost m + bGhost m * matterHalf m T = gaussSum m T := by
  classical
  have h1 : matterHalf m T * bGhost m
      = ∑ a : Fin 12, ∑ b : Fin 12,
          ghostCre m a * matterGen m T a * ghostAnn m b := by
    rw [matterHalf, bGhost, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have h2 : bGhost m * matterHalf m T
      = ∑ a : Fin 12, ∑ b : Fin 12,
          ghostAnn m b * (ghostCre m a * matterGen m T a) := by
    rw [matterHalf, bGhost, Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1, h2, gaussSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => pair_anticomm m T a b]
  rw [Finset.sum_ite_eq]
  simp

/-- **The anticommutator is `1` only if the gauge generators sum to the identity.**  Since the sum
of the Gauss generators is not the identity, the antighost contraction cannot be a homotopy for the
derivation: `b` contracts onto matter, which is exactly what §60 said the identification needs and
cannot have. -/
theorem bGhost_no_contraction (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (h : matterHalf m T * bGhost m + bGhost m * matterHalf m T = 1) : gaussSum m T = 1 := by
  rw [← bGhost_anticomm m T]
  exact h

/-- **On the abelian fibre the anticommutator vanishes.**  When the gauge generators sum to zero
there is no Gauss constraint to contract onto, and the index quartet of §57 — whose charge is the
ghost-only `Q` — is exactly that fibre.  This is why the quartet model is a comparison model for the
SM charge and not a subcomplex of it. -/
theorem bGhost_anticomm_abelian {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    (h0 : gaussSum m T = 0) :
    matterHalf m T * bGhost m + bGhost m * matterHalf m T = 0 := by
  rw [bGhost_anticomm m T, h0]

end BookProof.SmIndexGhostDerivation
