import Game.Metadata
import Game.MyNat.Multiplication
import Game.MyNat.TutorialLemmas

namespace MyNat

-- Proof Statement: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem skipped_add_zero_2 (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
-- Simplify the expression in the LHS (c + 0) to  c
  rw [add_zero c]
-- Prove LHS and RHS are equal, a + b + c = a + b + c, completing the proof
  rfl -- error

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem skipped_succ_eq_add_one n : succ n = n + 1 := by
  -- Rewrite RHS n + 1 as n + succ 0
  rw [one_eq_succ_zero]
  -- Prove LHS and RHS are equal, succ n = succ n, completing the proof
  rfl -- error

-- Proof Statement: Prove 2 + 2 = 4
theorem skipped_twoaddtwo : (2 : ℕ) + 2 = 4 := by
  -- Replace the second 2 in the LHS with succ 1, changing 2 + 2 to 2 + succ 1
  nth_rewrite 2 [two_eq_succ_one]
  -- Rewrite LHS from 2 + succ 1 to succ (2 + 1)
  rw [add_succ]
  -- Rewrite 1 as succ 0, so LHS changes from succ (2 + 1) to succ (2 + succ 0)
  rw [one_eq_succ_zero]
  -- Prove LHS and RHS are equal, succ (succ 2) = succ (succ 2), completing the proof
  rfl -- error



-- Skipped Steps Theorems Report:

-- skipped_add_zero_2: 1 steps skipped

-- skipped_succ_eq_add_one: 2 steps skipped

-- skipped_twoaddtwo: 4 steps skipped
