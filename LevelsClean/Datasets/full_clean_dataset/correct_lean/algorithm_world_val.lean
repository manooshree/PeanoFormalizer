import Game.LevelsClean.AdditionClean
-- import Game.Levels.Algorithm.L04add_algo3
import Game.LevelsClean.ImplicationClean
-- import Game.MyNat.DecidableEq

namespace MyNat


-- Deviation Log: 
-- Other: 
-- Proof Statement: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- Rewrite LHS using the commutative property of addition, changing a + (b + c) to a + b + c
  rw [← add_assoc]
  -- Rewrite LHS, swapping the order of a and b, changing a + b + c to b + a + c
  rw [add_comm a b]
  -- Rewrite LHS b + a + c as b + (a + c)
  rw [add_assoc]
  -- Prove LHS and RHS are equal, b + (a + c) = b + (a + c), completing the proof
  rfl

-- Deviation Log: Two premises combined into one tactic
-- Other: 
-- Proof Statement: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem add_left_comm_dev_1 (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- By associativity of addition, rewrite LHS a + (b + c) into a + b + c
  rw [← add_assoc]
  -- By the commutativity and associativity of addition, rewrite a + b + c to b + (a + c)
  rw [add_comm a b, add_assoc]
  -- So we just need to show b + (a + c) = b + (a + c), which is true by reflexivity and proof is complete.
  rfl

-- Proof Statement: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem add_left_comm_dev_2 (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- a + (b + c) = b + (a + c) -> a + b + c = b + (a + c)
  rw [← add_assoc]
  -- a + b + c = b + (a + c) -> a + b + c = a + b + c
  rw [← add_assoc]
  -- a + b + c = b + a + c
  rw [add_comm a b]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem var_swap (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- Apply the associative property of addition to both sides of the equation to regroup the terms to a + (b + (c + d)) = a + (c + (d + b))
  repeat rw [add_assoc]
  -- Rewrite LHS, swapping b and c in the term b + c, to get a + (c + (b + d))
  rw [add_left_comm b c]
  -- Rewrite LHS from a + (c + (b + d)) to a + (c + (d + b))
  rw [add_comm b d]
  -- Prove LHS and RHS are equal, a + (c + (d + b)) = a + (c + (d + b)), completing the proof
  rfl

-- Proof Statement: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem var_swap_dev_1 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- Use associativity of addition to change a + b + (c + d) into a + (b + (c + d)) and a + c + d + b into a + (c + (d + b))
  repeat rw [add_assoc]
  -- Change b + (c + d) into c + (b + d) using a previous theorem.
  rw [add_left_comm b c]
  -- Use commutativity of addition to change b + d into d + b
  rw [add_comm b d]
  -- So we must show that a + (c + (d + b)) = a + (c + (d + b)), which is true by reflexivity.
  rfl

-- Proof Statement: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem var_swap_dev_2 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- a + b + (c + d) = a + c + d + b -> a + (b + (c + d)) = a + (c + (d + b))
  repeat rw [add_assoc]
  -- a + (b + (c + d)) = a + (c + (d + b)) -> a + (c + (b + d)) = a + (c + (d + b))
  rw [add_left_comm b c]
  -- a + (c + (b + d)) = a + (c + (d + b)) -> a + (c + (d + b)) = a + (c + (d + b))
  rw [add_comm b d]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano (a b : ℕ) (h : succ a = succ b) : a = b := by
-- Rewrite a = b using the fact that the predecessor of the successor is itself, equation is now pred (succ a) = b
rw [← pred_succ a]
-- Rewrite the LHS pred (succ a) with the given statement that succ a = succ b, LHS is now pred (succ b)
rw [h]
-- Rewrite LHS from pred (succ b) succ b to using the fact that the predecessor of the successor of a number is the number itself
rw [pred_succ]
-- Prove LHS and RHS are equal, b = b, completing the proof
rfl

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano_dev_1 (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- We can change a into pred (succ a) in the goal a = b
  rw [← pred_succ a]
  -- Since succ a = succ b by hypothesis, we can instead show pred (succ b) = b
  rw [h]
  -- But we can change pred (succ b) into b.
  rw [pred_succ]
  -- So we must show b = b, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano_dev_2 (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- a = b -> pred (succ a) = b
  rw [← pred_succ a]
  -- pred (succ a) = b -> pred (succ b) = b
  rw [h]
  -- pred (succ b) = b -> b = b
  rw [pred_succ]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  -- Introduce the statement that succ a = 0 is false
  intro h
  -- Rewrite the proof goal to succ a = 0 if succ (a) is 0
  rw [← is_zero_succ a]
  -- Rewrite the proof goal to showing that succ a = 0 if 0 is zero
  rw [h]
  -- Simplify the if 0 is zero condition to true
  rw [is_zero_zero]
  -- We prove that our initial statement, of succ a = 0 is false, is indeed a true statement, completing the proof
  trivial

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero_dev_1 (a : ℕ) : succ a ≠ 0 := by
  -- To show succ a ≠ 0, we need to assume succ a = 0 and derive a contradiction/falsehood.
  intro h
  -- False and is_zero (succ 0) are equivalent, so we chose to show the latter.
  rw [← is_zero_succ a]
  -- By assumption, we can change succ a into 0.
  rw [h]
  -- is_zero 0 is equivalent to True, so we can show True instead.
  rw [is_zero_zero]
  -- True has the trivial proof.
  trivial

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero_dev_2 (a : ℕ) : succ a ≠ 0 := by
  -- assume succ a = 0
  intro h
  -- False -> is_zero (succ 0)
  rw [← is_zero_succ a]
  -- is_zero (succ 0) -> is_zero 0
  rw [h]
  -- is_zero 0 -> True
  rw [is_zero_zero]
  -- clearly, True
  trivial

-- Proof Statement: Prove the Peano axiom that if two natural numbers are not equal, their successors are not equal
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- Introduce the contrapositive, proving that m = n, given that succ m = succ n
  contrapose! h
  -- Simplify succ m = succ n to m = n, using the injectivity of the successor
  apply succ_inj at h
  -- We can exactly prove that m = n, with our given fact, to complete the proof
  exact h

-- Proof Statement: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem succ_ne_succ_dev_1 (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- We use proof by contraposition. So, we assume succ m = succ n and show m = n.
  contrapose! h
  -- By the injectivity of succ, we have m = n.
  apply succ_inj at h
  -- So, m = n, which is exactly what we wanted to show.
  exact h

-- Proof Statement: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem succ_ne_succ_dev_2 (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- proof by contraposition
  contrapose! h
  -- succ m = succ n -> m = n
  apply succ_inj at h
  -- m = n by hypothesis
  exact h
