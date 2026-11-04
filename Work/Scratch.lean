import Mathlib

example {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (c : ℂ) :
    ∑ m, ‖(if m = r then c else 0 : ℂ)‖ ^ 2 = ‖c‖ ^ 2 := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun m : ι => ‖(if m = r then c else 0 : ℂ)‖ ^ 2) r
    (fun m _ hm => by simp [hm])
    (fun h => absurd (Finset.mem_univ r) h)
  simpa using h
