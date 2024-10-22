import Mathlib.Data.Complex.Abs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Basic


inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

notation "ℕ" => MyNat

def one : MyNat := MyNat.succ MyNat.zero
def two : MyNat := MyNat.succ one

theorem one_eq_succ_zero : one = MyNat.succ MyNat.zero := by rfl
theorem two_eq_succ_one : two = MyNat.succ one := by rfl

namespace Tutorial_World

lemma level1_8 (x q : Nat ) : 37 * x  + q = 37 * x + q := by
  rfl

lemma level2_8 (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
  -- rfl

lemma level3_8 : two = MyNat.succ ( MyNat.succ MyNat.zero ):= by
  rw[two_eq_succ_one]
  rw [one_eq_succ_zero]
  -- rfl (commented out because lean has already noticed!)

lemma level4_8 : two = MyNat.succ ( MyNat.succ MyNat.zero ):= by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]
  -- rfl

lemma level5_8 (a b c : Nat) : a + (b + 0) + (c + 0)= a + b + c := by
  rw [add_zero]
  rw [add_zero]
  -- rfl

lemma level6_8 (a b c : Nat) : a + (b + 0) + (c + 0)= a + b + c := by --precision writing
  rw [add_zero c]
  rw [add_zero]
  --rfl



end Tutorial_World
