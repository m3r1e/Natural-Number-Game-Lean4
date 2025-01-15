

namespace Addition_World

lemma 1_5: (n : Nat) 0 + n = n := by
induction n with d hd
rw [addd_zero]
rw [add_succ]
rw [hd]
-- rfl
  



end Addition_World
