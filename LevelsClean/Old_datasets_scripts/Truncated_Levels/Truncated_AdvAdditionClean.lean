import Game.Levels.Implication
import Game.Levels.Algorithm
import Game.Levels.AdvAddition

namespace MyNat


-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem truncated_add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a + d = b + d. There are now two proof goals, prove base case: a + 0 = b + 0 and inductive step: a + succ (d) = b + succ (d) implies a = b.
  induction n with d hd
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = b + 0. The goal now is to prove that a = b.
  intro h
  -- Repeatedly apply the rewrite rule add_zero to the hypothesis h, which simplifies any terms of the form x + 0 in h to x. In this case
  repeat rw [add_zero] at h
  -- Apply the hypothesis 'h' to the goal, changing it to: if 'a + succ d' equals 'b + succ d', then 'a' equals 'b'
  exact h

-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem truncated_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  -- Rewrite the goal by repeatedly swapping the addition operands in the left side of both equations, changing n + a = n + b to a + n = b + n.
  repeat rw [add_comm n]
  -- Assume that the statement 'a + n = b + n' is true and denote it as 'h'. Then, our new goal is to prove that 'a = b'.
  intro h
  -- Simplify the hypothesis 'h' using the theorem 'add_right_cancel' assuming the theorem is true, which leaves the goal state unchanged as 'a = b'
  apply add_right_cancel at h

-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem truncated_add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  -- Assume that x + y = y as our hypothesis h, and then prove that x = 0.
  intro h
  -- Rewrite the second occurrence of the theorem 'zero_add y' in reverse in the hypothesis 'h', but the goal 'x = 0' remains unchanged.
  nth_rewrite 2 [← zero_add y] at h

theorem truncated_add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  -- Assume that x + y = x is true, then we need to prove that y = 0.
  intro h
  -- Rewrite the expression in hypothesis h using the add_comm theorem, which states that addition is commutative i.e., for all natural numbers a and b, a + b = b + a.
  rw [add_comm] at h

-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem truncated_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Split the natural number 'b' into two cases: 'b' is zero, and 'b' is the successor of another natural number 'd'.
  cases b with d
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = 0. The goal now is to prove that a = 0.
  intro h
  -- Repeatedly apply the theorem that adding zero to any number does not change its value to the hypothesis h.
  rw [add_zero] at h

theorem truncated_add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  -- Rewrite the goal by swapping the addition operands in the left side of both equations, changing a + b = 0 to b + a = 0.
  rw [add_comm]
  -- Apply the theorem that states that if a + b = 0, then b = 0 for all natural numbers.
  exact add_right_eq_zero b a


-- Truncated Theorems Report:

-- truncated_add_right_cancel: 4 steps kept

-- truncated_add_left_cancel: 3 steps kept

-- truncated_add_left_eq_self: 2 steps kept

-- truncated_add_right_eq_self: 2 steps kept

-- truncated_add_right_eq_zero: 3 steps kept

-- truncated_add_left_eq_zero: 2 steps kept
