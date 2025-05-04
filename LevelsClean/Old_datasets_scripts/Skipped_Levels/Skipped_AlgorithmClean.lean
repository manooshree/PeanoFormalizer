import Game.Levels.Addition
-- import Game.Levels.Algorithm.L04add_algo3
import Game.Levels.Implication
-- import Game.MyNat.DecidableEq

World "Algorithm"
Level 5

namespace MyNat


-- Proof Statement: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem skipped_add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- Rewrite LHS using the commutative property of addition, changing a + (b + c) to a + b + c
  rw [← add_assoc]
  -- Rewrite LHS, swapping the order of a and b, changing a + b + c to b + a + c
  rw [add_comm a b]
  -- Prove LHS and RHS are equal, b + (a + c) = b + (a + c), completing the proof
  rfl -- error

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem skipped_succ_peano (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- Rewrite a = b using the fact that the predecessor of the successor is itself, equation is now pred (succ a) = b
  rw [← pred_succ a]
  -- Rewrite LHS from pred (succ b) succ b to using the fact that the predecessor of the successor of a number is the number itself
  rw [pred_succ]
  -- Prove LHS and RHS are equal, b = b, completing the proof
  rfl -- error

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem skipped_succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  -- Introduce the statement that succ a = 0 is false
  intro h
  -- By assumption, we can change succ a into 0.
  rw [h] -- error
  -- is_zero 0 is equivalent to True, so we can show True instead.
  rw [is_zero_zero]
  -- True has the trivial proof.
  trivial




-- Skipped Steps Theorems Report:

-- skipped_add_left_comm: 1 steps skipped

-- skipped_succ_peano: 1 steps skipped

-- skipped_succ_ne_zero: 1 steps skipped
