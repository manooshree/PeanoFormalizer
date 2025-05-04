import Game.LevelsClean.LessOrEqualClean
import Game.LevelsClean.MultiplicationClean

namespace MyNat

-- Theorem Declaration: Prove that if a is less than or equal to b, then a times t is less than or equal to b times t.
theorem mul_le_mul_right__dev_1 (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We know that a ≤ b, so we can express b as a + d for some natural number d.
  cases h with d hd
  -- Rewrite b as a + d using the previous statement
  rw [hd]
  -- simplify to a * t ≤ a * t + d * t using the distributive property of multiplication over addition
  rw [add_mul]
  -- The LHS and RHS are equal, completing the proof
  rfl

-- Theorem Declaration: Prove that if a is less than or equal to b, then a times t is less than or equal to b times t.
theorem mul_le_mul_right__dev_2 (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We know that a ≤ b, so we can express b as a + d for some natural number d.
  cases h with d hd
  -- subsitute b with a + d using what we haven shown above and apply the distributive property of multiplication over addition
  rw [hd, add_mul]
  -- The LHS and RHS are equal, completing the proof
  rfl

-- Theorem Declaration: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem mul_left_ne_zero__dev_1 (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0.
  intro hb
  -- a * b = 0 -> a * 0 = 0 -> 0 = 0
  rw [hb, mul_zero]
  -- We use reflexivity to prove the goal of 0 = 0.
  rfl

-- Theorem Declaration: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem mul_left_ne_zero__dev_2 (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0.
  intro hd
  -- a * 0 != 0 -> 0 != 0
  rw [mul_zero] at h
  -- We have 0 != 0 which is a contradiction.
  tauto

-- Theorem Declaration: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem eq_succ_of_ne_zero__dev_1 (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- We use reflexivity to prove that 'succ d' equals 'succ d'.
  rfl

-- Theorem Declaration: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem eq_succ_of_ne_zero__dev_2 (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- Since the LHS and RHS are equal, we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero__dev_1 (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- a is either 0 or the successor of some natural number d.
  cases a with d
  -- When a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- 1 <= d + 1 -> 1 + d = d + 1
  use d
  -- 1 + d = d + 1 -> 1 + d = 1 + d
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero__dev_2 (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- we know that 1 <= succ d -> 1 <= d + 1
  rw [succ_eq_add_one]
  -- 1 <= d + 1 -> 1 + a = d + 1 where a is some natural number by the definition of inequality. set a to be d.
  use d
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right__dev_1 (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- b is either 0 or the successor of some natural number d.
  cases b with d
  -- a * 0 != 0 -> 0 != 0
  rw [mul_zero] at h
  -- 0 != 0 is false so the theorem doesn't hold for this case.
  tauto
  -- a <= a * succ d -> a <= a * d + a
  rw [mul_succ]
  -- a * d + a = a + a * d -> a * d + a = a + a * d
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right__dev_2 (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- proof by induction on b
  induction b with d _
  -- for the base case, a * 0 != 0 -> 0 != 0
  apply mul_left_ne_zero at h
  -- 0 != 0 is false so the theorem doesn't hold for this case.
  tauto
  -- a <= a * d + a -> a * d + a = a + a * d by the definition of inequality, if we set a * d to be a.
  use a * d
  -- a * d + a = a + a * d -> a * d + a = a + a * d by the commutative property of addition.
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one__dev_1 (x y : ℕ) (h : x * y = 1) : x = 1 := by
  -- assume that x * y is not equal to 0
  have h2 : x * y ≠ 0
  -- rewrite the goal with the previous assumption so the new goal is 1 is not equal to 0
  rw [h]
  -- We know that 1 is not equal to 0, so we can use this to prove the goal.
  exact one_ne_zero
  -- We have shown that for any natural number x, if x * y not equal to 0, x <= x * y. so we know that x ≤ x * y
  apply le_mul_right at h2
  -- We are given that x * y = 1, so we know that x ≤ 1
  rw [h] at h2
  -- Since x <= 1, x must be 1 or 0.
  apply le_one at h2
  -- We consider the two possible cases for x given by the disjunction in h2: either x equals 0 or x equals 1.
  cases h2 with h0 h1
  -- we know that x * y = 1. Plugging in x = 0, we get 0 * y = 0.
  rw [h0] at h
  -- we know that 0 * n = 0 for any natural number n, so we have 0 = 1.
  rw [zero_mul] at h
  -- We have shown that x = 1 which proves the goal.
  tauto

-- Theorem Declaration: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one__dev_2 (x y : ℕ) (h : x * y = 1) : x = 1 := by
  -- assume that x * y is not equal to 0
  have h2 : x * y ≠ 0
  -- rewrite the goal with the previous assumption so the new goal is 1 is not equal to 0
  rw [h]
  -- We know that 1 is not equal to 0, so we can use this to prove the goal.
  exact one_ne_zero
  -- x * y != 0 -> x <= x * y
  apply le_mul_right at h2
  -- x <= x * y -> x <= 1
  rw [h] at h2
  -- x <= 1 -> x = 0 or x = 1
  cases x
  -- for the x = 0 case, 0 * y = 1 -> 0 = 1
  rw [zero_mul] at h
  -- 0 = 1 is false, so we can use this to show that x is not equal to 0.
  tauto
  -- for the x = 1 case, succ a ≤ 1 -> succ a = 0 ∨ succ a = 1
  apply le_one at h2
  -- Let's look at the two possible cases for h2: either succ a = 0 or succ a = 1
  cases h2 with h0 h1
  -- 0 = 1 is false, so we can use this to show that x is not equal to 0.
  tauto
  -- for the succ a = 1 case, succ a = 1 -> 1 = 1
  rw [h1]
  -- 1 = 1 is true by reflexivity
  rfl

-- Theorem Declaration: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem mul_ne_zero__dev_1 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- Since a is a natural number, it is either 0 or the successor of some natural number.
  cases a with a
  -- If a is 0, this theorem doesn't hold.
  tauto
  -- succ a * succ b ≠ 0 -> succ a * b + succ a ≠ 0 by the definition of multiplication
  rw [succ_mul]
  -- Since b is a natural number, it is either 0 or the successor of some natural number.
  cases b with b
  -- If b is 0, this theorem doesn't hold.
  tauto
  -- succ a * b + succ a ≠ 0 -> succ (succ a * b + a) ≠ 0 by the definition of addition
  rw [add_succ]
  -- We know that 0 is not equal to the successor of any natural number, so we can use this to prove the goal.
  apply zero_ne_succ

-- Theorem Declaration: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem mul_ne_zero__dev_2 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- Since a is a natural number, it is either 0 or the successor of some natural number.
  cases a with a
  -- If a is 0, this theorem doesn't hold.
  tauto
  -- Since b is a natural number, it is either 0 or the successor of some natural number.
  cases b with b
  -- If b is 0, this theorem doesn't hold.
  tauto
  -- succ a * succ b ≠ 0 -> succ a * b + succ a ≠ 0
  rw [mul_succ]
  -- succ (succ a * b + a) ≠ 0 -> 0 ≠ succ (succ a * b + a)
  symm
  -- We know that 0 is not equal to the successor of any natural number, so we can use this to prove the goal.
  apply zero_ne_succ

-- Theorem Declaration: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem mul_eq_zero__dev_1 (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- We introduce a new fact stating that if neither a nor b is zero, then their product cannot be zero.
  have h2 := mul_ne_zero a b
  -- a * b ≠ a * b is a contradiction, so either a = 0 or b = 0
  tauto

-- Theorem Declaration: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem mul_eq_zero__dev_2 (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- We introduce a new fact stating that if neither a nor b is zero, then their product cannot be zero.
  have h2 := mul_ne_zero a b
  -- 0 ≠ 0 is a contradiction, so either a = 0 or b = 0
  tauto

-- Theorem Declaration: Prove that if a times b is equal to a times c, then b is equal to c.
theorem mul_left_cancel__dev_1 (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  -- proof by induction on b
  induction b with d hd generalizing c
  -- for the base case, a * 0 = a * c -> 0 = a * c by the definition of multiplication
  rw [mul_zero] at h
  -- 0 = a * c -> a * c = 0 by the symmetry property of equality
  symm at h
  -- a * c = 0 -> a = 0 ∨ c = 0 by the fact that if a times b is equal to 0, then either a is equal to 0 or b is equal to 0.
  apply mul_eq_zero at h
  -- either a is equal to 0 or c is equal to 0.
  cases h with h1 h2
  -- if a is equal to 0, then we have a contradiction.
  tauto
  -- if c is equal to 0, then we have that 0 = 0.
  rw [h2]
  -- 0 = 0 closes the base case.
  rfl
  -- consider two subcases for c: when c is 0 and when c is a successor of another natural number e.
  cases c with e he
  -- a * succ d = a * 0 -> a * succ d = 0 by the definition of multiplication
  rw [mul_zero] at h
  -- a * succ d = 0 -> a * succ d = 0 by the properties of multiplication
  apply mul_eq_zero at h
  -- either a is equal to 0 or c is equal to 0.
  cases h with h1 h2
  -- if a is equal to 0, then we have a contradiction.
  tauto
  -- if c = 0, then we have that ucc d  = 0.
  exact h2
  -- a * succ d = a * succ e -> a * d + a = a * succ e -> a * d + a = a * e + a by the definition of multiplication
  rw [mul_succ, mul_succ] at h
  -- a * d + a = a * e + a -> a * d = a * e by properties of addition
  apply add_right_cancel at h
  -- a * d = a * e -> d = e by the induction hypothesis
  apply hd at h
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a times b is equal to a times c, then b is equal to c.
theorem mul_left_cancel__dev_2 (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  -- proof by induction on b
  induction b with d hd generalizing c
  -- for the base case, a * 0 = a * c -> 0 = a * c
  rw [mul_zero] at h
  -- 0 = a * c -> a * c = 0
  symm at h
  -- a * c = 0 -> a = 0 ∨ c = 0
  apply mul_eq_zero at h
  -- either a is equal to 0 or c is equal to 0.
  cases h with h1 h2
  -- if a is equal to 0, then we have a contradiction.
  tauto
  -- if c is equal to 0, then we have that 0 = 0.
  rw [h2]
  -- 0 = 0 closes the base case.
  rfl
  -- consider two subcases for c: when c is 0 and when c is a successor of another natural number e.
  cases c with e he
  -- a * succ d = a * 0 -> a * succ d = 0
  rw [mul_zero] at h
  -- a * succ d = 0 -> a * succ d = 0
  apply mul_eq_zero at h
  -- either a is equal to 0 or c is equal to 0.
  cases h with h1 h2
  -- if a is equal to 0, then we have a contradiction.
  tauto
  -- if c = 0, then we have that ucc d  = 0.
  exact h2
  -- a * succ d = a * succ e -> a * d + a = a * succ e -> a * d + a = a * e + a
  rw [mul_succ, mul_succ] at h
  -- a * d + a = a * e + a -> a * d = a * e
  apply add_right_cancel at h
  -- succ d = succ e -> succ e = succ d
  rw [h]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Theorem Declaration: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem mul_right_eq_self__dev_1 (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  -- Since b is a natural number, it is either 0 or the successor of some natural number.
  cases b with d hd
  -- 0 = a is a contradiction, so we don't need to consider this case.
  tauto
  -- if a is not equal to 0, then a * succ d = a -> a * succ d = a * 1
  nth_rewrite 2 [← mul_one a] at h
  -- by properties of multiplication, we know that this implication is true.
  exact mul_left_cancel a (succ d) 1 ha h

-- Theorem Declaration: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem mul_right_eq_self__dev_2 (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  --  a * b = a -> a * 1 * b = a * 1
  rw [← mul_one a] at h
  -- a * (1 * b) = a * 1 -> a * b = a * 1
  rw [one_mul b] at h
  -- Apply the the theorem that states that for all natural numbers a and b, a times b is equal to a times c, then b is equal to c which shows that b = 1.
  exact mul_left_cancel a b 1 ha h

end MyNat
