import Game.Levels.Implication
import Game.Levels.Algorithm


World "AdvAddition"
Level 1
Title "add_right_cancel"
namespace MyNat


-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem skipped_add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a + d = b + d. There are now two proof goals, prove base case: a + 0 = b + 0 and inductive step: a + succ (d) = b + succ (d) implies a = b.
  induction n with d hd
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = b + 0. The goal now is to prove that a = b.
  intro h
  -- Repeatedly apply the rewrite rule add_zero to the hypothesis h, which simplifies any terms of the form x + 0 in h to x. In this case
  repeat rw [add_zero] at h
  -- Apply the hypothesis 'h' to the goal, changing it to: if 'a + succ d' equals 'b + succ d', then 'a' equals 'b'
  exact h
  -- Introduce a hypothesis h: a + succ d = b + succ d. Now the goal is to prove a = b given this hypothesis.
  intro h
  -- h proves the goal a = b so we can use it to finish the proof
  exact h -- error

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem skipped_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  -- Rewrite the goal by repeatedly swapping the addition operands in the left side of both equations, changing n + a = n + b to a + n = b + n.
  repeat rw [add_comm n]
  -- Simplify the hypothesis 'h' using the theorem 'add_right_cancel' assuming the theorem is true, which leaves the goal state unchanged as 'a = b'
  apply add_right_cancel at h -- error
  -- h proves the goal a = b so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem skipped_add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  -- Assume that x + y = y as our hypothesis h, and then prove that x = 0.
  intro h
  -- If a + n = b + n, then a = b. So, in our case, if x + y = 0 + y, then x = 0.
  apply add_right_cancel at h -- error
  -- h proves the goal x = 0 so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem skipped_add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  -- Assume that x + y = x is true, then we need to prove that y = 0.
  intro h
  -- Rewrite the expression in hypothesis h using the add_comm theorem, which states that addition is commutative i.e., for all natural numbers a and b, a + b = b + a.
  rw [add_comm] at h
  -- h proves the goal y = 0 so we can use it to finish the proof
  exact h -- error


-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem skipped_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Split the natural number 'b' into two cases: 'b' is zero, and 'b' is the successor of another natural number 'd'.
  cases b with d
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = 0. The goal now is to prove that a = 0.
  intro h
  -- For any natural numbers x and y, x + succ y = succ (x + y). Applying this repeatedly simplifies the hypothesis but leaves the goal state a = 0 unchanged.
  rw [add_succ] at h -- error
  -- Swap the left-hand side and the right-hand side of the equality in the hypothesis.
  symm at h
  -- Apply the theorem that states that the successor of any natural number cannot equal 0 to our hypothesis h which shows that h is false.
  apply zero_ne_succ at h
  -- Since h is a proof of False, and there are no ways to construct False so we have our contradiction and can close the proof
  cases h


end MyNat



-- Skipped Steps Theorems Report:

-- skipped_add_right_cancel: 3 steps skipped

-- skipped_add_left_cancel: 1 steps skipped

-- skipped_add_left_eq_self: 1 steps skipped

-- skipped_add_right_eq_self: 1 steps skipped

-- skipped_add_right_eq_zero: 3 steps skipped
