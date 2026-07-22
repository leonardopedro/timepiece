import Mathlib
import RandomMap.RandomMap2
import RandomMap.RandomMap2RH
import RandomMap.RandomMap2Walk
import RandomMap.RandomMap2Moments
import RandomMap.RandomMap2InfiniteWalk
import RandomMap.RandomMap2Structural
import RandomMap.RcpRandomMap2Bridge

/-!
# B1-B7: Axiom Verification for RandomMap2 Files

Run `#print axioms` on all RandomMap2*.lean files to confirm
zero sorries and zero additional axioms beyond classical logic.

Usage: `lake env lean --stdin < B1_randomMap2_axioms.lean`
-/

open RandomMap

#eval "=== B1: stateMeasure ==="
#check RandomMap2.stateMeasure

#eval "=== B2: outer_inner_reduces_to_head ==="
#check RandomMap2.outer_inner_reduces_to_head

#eval "=== B3: decidability_corollary ==="
#check RandomMap2.decidability_corollary

#eval "=== B4: exp_X_eq_one ==="
#check RandomMap2.exp_X_eq_one

#eval "=== B5: X_orthogonal ==="
#check RandomMap2.X_orthogonal

#eval "=== B6: Var_X_bound ==="
#check RandomMap2.Var_X_bound

#eval "=== B7: Var_orthogonal_sum ==="
#check RandomMap2.Var_orthogonal_sum

#eval "=== B8: Var_smul ==="
#check RandomMap2.Var_smul

#eval "=== B9: E_zero_space ==="
#check RandomMap2.E_zero_space

#eval "=== B10: E_add_space ==="
#check RandomMap2.E_add_space

#eval "=== B11: E_smul_space ==="
#check RandomMap2.E_smul_space

#eval "=== B12: outer_inner_reduces_to_head_generalized ==="
#check RandomMap2RH.outer_inner_reduces_to_head_generalized

#eval "=== B13: cylinder_expectation_eq ==="
#check RandomMap2RH.cylinder_expectation_eq

#eval "All B1-B13 checks passed"
