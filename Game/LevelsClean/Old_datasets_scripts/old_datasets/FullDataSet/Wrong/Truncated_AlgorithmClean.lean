import Game.Levels.Addition
import Game.Levels.Implication
import Game.Levels.Algorithm


namespace MyNat


-- Proof Statement: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem truncated_add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- Rewrite LHS using the commutative property of addition, changing a + (b + c) to a + b + c
  rw [← add_assoc]
  -- Rewrite LHS, swapping the order of a and b, changing a + b + c to b + a + c
  rw [add_comm a b]

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem truncated_var_swap (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- Apply the associative property of addition to both sides of the equation to regroup the terms to a + (b + (c + d)) = a + (c + (d + b))
  repeat rw [add_assoc]
  -- Rewrite LHS, swapping b and c in the term b + c, to get a + (c + (b + d))
  rw [add_left_comm b c]

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem truncated_succ_peano (a b : ℕ) (h : succ a = succ b) : a = b := by
-- Rewrite a = b using the fact that the predecessor of the successor is itself, equation is now pred (succ a) = b
rw [← pred_succ a]
-- Rewrite the LHS pred (succ a) with the given statement that succ a = succ b, LHS is now pred (succ b)
rw [h]

-- Proof Statement: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem truncated_succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  -- Introduce the statement that succ a = 0 is false
  intro h
  -- Rewrite the proof goal to succ a = 0 if succ (a) is 0
  rw [← is_zero_succ a]
  -- Rewrite the proof goal to showing that succ a = 0 if 0 is zero
  rw [h]
  -- Simplify the if 0 is zero condition to true
  rw [is_zero_zero]

theorem truncated_succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- Introduce the contrapositive, proving that m = n, given that succ m = succ n
  contrapose! h
  -- Simplify succ m = succ n to m = n, using the injectivity of the successor
  apply succ_inj at h


-- Truncated Theorems Report:

-- truncated_add_left_comm: 2 steps kept

-- truncated_var_swap: 2 steps kept

-- truncated_succ_peano: 2 steps kept

-- truncated_succ_ne_zero: 4 steps kept

-- truncated_succ_ne_succ: 2 steps kept
