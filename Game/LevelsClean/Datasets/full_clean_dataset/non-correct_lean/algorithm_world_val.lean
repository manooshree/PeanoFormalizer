import Game.LevelsClean.AdditionClean
-- import Game.Levels.Algorithm.L04add_algo3
import Game.LevelsClean.ImplicationClean
-- import Game.MyNat.DecidableEq

namespace MyNat

-- Theorem Declaration: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem add_left_comm_dev_1 (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- By associativity of addition, can change a + (b + c) into (a + b) + c
  rw [← add_assoc]
  -- By the associativity of addition, can change (b + a) + c into b + (a + c)
  rw [add_assoc]
  -- So we just need to show b + (a + c) = b + (a + c), which is true by reflexivity.
  rfl

-- Theorem Declaration: Prove that for natural numbers a, b, and c, a + (b + c) = b + (a + c).
theorem add_left_comm_dev_2 (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- a + (b + c) = b + (a + c) -> (a + b) + c = b + (a + c)
  rw [← add_assoc]
  -- (a + b) + c = b + (a + c) -> (b + a) + c = b + (a + c)
  rw [add_comm a b]
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem var_swap_dev_1 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- Use associativity of addition to change a + b + (c + d) into a + (b + (c + d)) and a + c + d + b into a + (c + (d + b))
  repeat rw [add_assoc]
  -- Change b + (c + d) into c + (b + d) using a previous theorem.
  rw [add_left_comm b c]
  -- So we must show that a + (c + (d + b)) = a + (c + (d + b)), which is true by reflexivity.
  rfl

-- Theorem Declaration: Prove (a + b) + (c + d) = ((a + c) + d) + b for natural numbers a, b, c, d
theorem var_swap_dev_2 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- a + b + (c + d) = a + c + d + b -> a + (b + (c + d)) = a + (c + (d + b))
  repeat rw [add_assoc]
  -- a + (b + (c + d)) = a + (c + (d + b)) -> a + (c + (b + d)) = a + (c + (d + b))
  rw [add_left_comm b c]
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano_dev_1 (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- We can change a into pred (succ a) in the goal a = b
  rw [← pred_succ a]
  -- Since succ a = succ b by hypothesis, we can instead show pred (succ b) = b
  rw [h]
  -- So we must show b = b, which is true by reflexivity.
  rfl

-- Theorem Declaration: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano_dev_2 (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- a = b -> pred (succ a) = b
  rw [← pred_succ a]
  -- pred (succ b) = b -> b = b
  rw [pred_succ]
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero_dev_1 (a : ℕ) : succ a ≠ 0 := by
  -- To show succ a ≠ 0, we need to assume succ a = 0 and derive a contradiction/falsehood.
  intro h
  -- False and is_zero (succ 0) are equivalent, so we chose to show the latter.
  rw [← is_zero_succ a]
  -- By assumption, we can change succ a into 0.
  rw [h]
  -- True has the trivial proof.
  trivial

-- Theorem Declaration: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero_dev_2 (a : ℕ) : succ a ≠ 0 := by
  -- assume succ a = 0
  intro h
  -- is_zero (succ 0) -> is_zero 0
  rw [h]
  -- is_zero 0 -> True
  rw [is_zero_zero]
  -- clearly, True
  trivial

-- Theorem Declaration: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem succ_ne_succ_dev_1 (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- We use proof by contraposition. So, we assume succ m = succ n and show m = n.
  contrapose! h
  -- So, m = n, which is exactly what we wanted to show.
  exact h

-- Theorem Declaration: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem succ_ne_succ_dev_2 (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- proof by contraposition
  contrapose! h
  -- m = n by hypothesis
  exact h

end MyNat
