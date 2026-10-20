import Mathlib

/-!
# Shim: platform-Mathlib summation lemmas missing from the pinned Mathlib

`hasSum_ite_eq'` / `tsum_ite_eq'` are the variants of `hasSum_ite_eq` / `tsum_ite_eq` with the
equality written `b = b'` instead of `b' = b`.  Both are proved here from the pinned API.
-/

variable {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]

theorem hasSum_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) :
    HasSum (fun b' => if b = b' then a else 0) a := by
  classical
  convert hasSum_ite_eq b a using 2 with b'
  exact if_congr eq_comm rfl rfl

theorem tsum_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β → α) :
    ∑' b', (if b = b' then a b' else 0) = a b := by
  classical
  rw [← tsum_ite_eq b a]
  exact tsum_congr fun b' => if_congr eq_comm rfl rfl
