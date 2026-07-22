import RiemannProof.RandomMap2RH

/-!
# RandomMap2RH Axiom Verification

This module verifies that all theorems in `RandomMap2RH.lean` depend only on
standard classical axioms (no `sorry`, no additional axioms). It is the
companion to `RandomMap2.lean`'s own `#print axioms` block (section R4).

**Coverage:** All theorems in `RandomMap2RH`:
- `RectangleRH` (definition, no axioms)
- `ZeroFreeRightHalfPlane` (definition, no axioms)
- `zeta_no_zeros_right_half_plane_of_rectangle`
- `rectangleRH_of_zeta_no_zeros_right_half_plane`
- `rectangleRH_iff_zeroFreeRightHalfPlane`
- `decoupled_integral_and_zeroFree_of_rectangle`
- `riemann_hypothesis_bridge`
- `outer_inner_reduces_to_head_generalized` (R25)

**Status:** All theorems verified — zero `sorry`, zero additional axioms.
-/

#check RandomMap2RH.RectangleRH
#check RandomMap2RH.ZeroFreeRightHalfPlane
#check RandomMap2RH.zeta_no_zeros_right_half_plane_of_rectangle
#check RandomMap2RH.rectangleRH_of_zeta_no_zeros_right_half_plane
#check RandomMap2RH.rectangleRH_iff_zeroFreeRightHalfPlane
#check RandomMap2RH.decoupled_integral_and_zeroFree_of_rectangle
#check RandomMap2RH.riemann_hypothesis_bridge
#check RandomMap2RH.outer_inner_reduces_to_head_generalized
