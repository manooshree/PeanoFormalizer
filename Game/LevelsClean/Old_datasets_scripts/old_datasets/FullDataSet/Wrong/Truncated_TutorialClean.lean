import Game.Metadata
import Game.MyNat.Multiplication
import Game.MyNat.TutorialLemmas

namespace MyNat


-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem truncated_two_eq_ss0: 2 = succ (succ 0) := by
   -- Use the fact that the successor of 1, succ 1, is 2, in the proof goal, changing the equation to 'succ 1 = succ (succ 0)'
  rw [two_eq_succ_one]
  -- Use the fact that 1 = succ 0 and expand the LHS succ (succ 0), changing the equation to succ (succ 0) = succ (succ 0)
  rw [one_eq_succ_zero]

-- Proof Statement: Prove that 2 = succ (succ 0)
theorem truncated_rw_backwards : 2 = succ (succ 0) := by
  -- Simplify succ 0 to 1, changing RHS from succ (succ 0) to succ 1
  rw [← one_eq_succ_zero]
  -- Simplify succ 1 to 2, changing RHS from succ 1 to 2
  rw [← two_eq_succ_one]

-- Proof Statement: Prove that a + 0 = a for all natural numbers a
theorem truncated_add_zero_intro (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Simplify the expression in the LHS (b + 0) to  b
  rw [add_zero]
  -- Simplify the expression in the LHS (c + 0) to c
  rw [add_zero]

-- Proof Statement: Prove that a + (b + 0) + (c + 0) = a + b + c
theorem truncated_add_zero_intro_2 (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
-- Simplify the expression in the LHS (c + 0) to  c
  rw [add_zero c]
-- Simplify the expression in the LHS (c + 0) to  c
  rw [add_zero b]


-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem trancated_succ_eq_add_one n : succ n = n + 1 := by
  -- Rewrite RHS n + 1 as n + succ 0
  rw [one_eq_succ_zero]
  -- Rewrite RHS from n + succ 0 to succ (n + 0)
  rw [add_succ]
  -- Simplify RHS succ (n + 0) to succ n
  rw [add_zero]

-- Proof Statement: Prove that 2 + 2 = 4
theorem truncated_twoaddtwo : (2 : ℕ) + 2 = 4 := by
  -- Replace the second 2 in the LHS with succ 1, changing 2 + 2 to 2 + succ 1
  nth_rewrite 2 [two_eq_succ_one]
  -- Rewrite LHS from 2 + succ 1 to succ (2 + 1)
  rw [add_succ]


-- Truncated Theorems Report:

-- truncated_two_eq_ss0: 2 steps kept

-- truncated_rw_backwards: 2 steps kept

-- truncated_add_zero_intro: 2 steps kept

-- truncated_add_zero_2: 2 steps kept

-- trancated_succ_eq_add_one: 3 steps kept

-- truncated_twoaddtwo: 2 steps kept
