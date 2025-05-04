import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1
Title "mul_le_mul_right"

TheoremTab "*"

namespace MyNat

-- Proof Statement: Prove that if a is less than or equal to b, then a times t is less than or equal to b times t.
theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We consider the case where the inequality a ≤ b can be expressed as b being equal to a plus some natural number d.
  cases h with d hd
  -- We use d * t as a specific natural number that can be used to rewrite a * t ≤ b * t as b * t = a * t + d * t.
  use d * t
  -- We know that b = a + d, so we can substitute b with a + d in the goal. Then rewrite the goal as a * t + d * t ≤ a * t + d * t by the distributive property of multiplication over addition.
  rw [hd, add_mul]
  -- We have that a * t + d * t = a * t + d * t, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is less than or equal to b, then a times t is less than or equal to b times t.
theorem mul_le_mul_right_train1 (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We know that a ≤ b, so we can express b as a + d for some natural number d.
  cases h with d hd
  -- Rewrite b as a + d using the previous statement
  rw [hd]
  -- simplify to a * t ≤ a * t + d * t using the distributive property of multiplication over addition
  rw [add_mul]
  -- Use d * t as a specific natural number that can be used to rewrite a * t ≤ b * t as b * t = a * t + d * t.
  use d * t
  -- The LHS and RHS are equal, completing the proof
  rfl

-- Proof Statement: Prove that if a is less than or equal to b, then a times t is less than or equal to b times t.
theorem mul_le_mul_right_test (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We know that a ≤ b, so we can express b as a + d for some natural number d.
  cases h with d hd
  -- set d to be d * t and simplify the inequality to b * t = a * t + d * t
  use d * t
  -- subsitute b with a + d using what we haven shown above and apply the distributive property of multiplication over addition
  rw [hd, add_mul]
  -- The LHS and RHS are equal, completing the proof
  rfl

-- Proof Statement: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0. The goal is now to show that this leads to a contradiction.
  intro hd
  -- We are given that a * b ≠ 0, the negation of this is a * b = 0, if we prove this we will have a contradiction.
  apply h
  -- We know that b = 0, so we can substitute b with 0 in the goal. Then, multipling a natural number a by 0 gives us 0, so our new goal is 0 = 0.
  rw [hd, mul_zero]
  -- We use reflexivity to prove the goal of 0 = 0.
  rfl

-- Proof Statement: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem mul_left_ne_zero_train1 (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0.
  intro hb
  -- Have to show that a * b = 0
  apply h
  -- a * b = 0 -> a * 0 = 0 -> 0 = 0
  rw [hb, mul_zero]
  -- We use reflexivity to prove the goal of 0 = 0.
  rfl

-- Proof Statement: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem mul_left_ne_zero_test (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0.
  intro hd
  -- subtitute b with 0 which gives us a * 0 != 0
  rw [hd] at h
  -- a * 0 != 0 -> 0 != 0
  rw [mul_zero] at h
  -- We have 0 != 0 which is a contradiction.
  tauto

-- Proof Statement: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We consider two cases for a: when a is zero and when a is the successor of another natural number.
  cases a with d
  -- By logical reasoning, we know that 0 cannot be equal to 0, which is a contradiction. Therefore, there is no natural number such that 0 is the successor of that number so we can close the case where a is 0.
  tauto
  -- We provide an example where the natural number 'd' satisfies the condition that 'succ d' equals 'succ n'.
  use d
  -- We use reflexivity to prove that 'succ d' equals 'succ d'.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem eq_succ_of_ne_zero_train1 (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- For the inductive step, we set n to be d.
  use d
  -- We use reflexivity to prove that 'succ d' equals 'succ d'.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem eq_succ_of_ne_zero_test (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- For the inductive step, we set n to be d which gives us succ d = succ d
  use d
  -- Since the LHS and RHS are equal, we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- We use the previous lemma to express a as the successor of some natural number n since a is not equal to 0.
  apply eq_succ_of_ne_zero at ha
  -- Simplify the hypothesis to say that a is the successor of some natural number n.
  cases ha with d hd
  -- 1 <= a means that there exists some natural number m such that 1 + m = a. We use n as the natural number m.
  use d
  -- We showed that a = succ n, so we can rewrite the goal as succ n = 1 + n.
  rw [hd]
  -- Rewrite 'succ n' as '1 + n'
  rw [succ_eq_add_one]
  -- Switch the order of addition to match the goal '1 + n = 1 + n'
  rw [add_comm]
  -- We have that 1 + n = 1 + n, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero_train1 (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- a is either 0 or the successor of some natural number d.
  cases a with d
  -- When a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- 1 <= succ d -> 1 <= d + 1
  rw [succ_eq_add_one]
  -- 1 <= d + 1 -> 1 + d = d + 1
  use d
  -- 1 + d = d + 1 -> 1 + d = 1 + d
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero_test (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- We use induction on a.
  induction a with d _
  -- For the base case, a = 0, the theorem doesn't hold because we know a != 0.
  tauto
  -- we know that 1 <= succ d -> 1 <= d + 1
  rw [succ_eq_add_one]
  -- 1 <= d + 1 -> 1 + a = d + 1 where a is some natural number by the definition of inequality. set a to be d.
  use d
  -- 1 + d = d + 1 -> 1 + d = 1 + d by the commutative property of addition.
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero_test2 (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- sing the fact that 'a' is not zero, we express 'a' as the successor of some natural number 'n'.
  apply eq_succ_of_ne_zero at ha
  -- Simplify the hypothesis to say that a is the successor of some natural number n.
  cases ha with n hn
  -- 1 <= a means that there exists some natural number m such that 1 + m = a. We use n as the natural number m.
  use n
  -- We showed that a = succ n, so we can rewrite the goal as succ n = 1 + n. Then rewrite 'succ n' as '1 + n' and switch the order of addition to match the goal '1 + n = 1 + n'
  rw [hn, succ_eq_add_one, add_comm]
  -- We have that 1 + n = 1 + n, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- We are given that the product of a and b is not zero. Therefore, we can conclude that b is not zero.
  apply mul_left_ne_zero at h
  -- We showed that b is not zero, so we can use this to show that b is at least 1.
  apply one_le_of_ne_zero at h
  -- We showed that b is at least 1, so we can use this to show that a * 1 <= a * b.
  apply mul_le_mul_right 1 b a at h
  -- We showed that a * 1 <= a * b. We can change 1 * a to just a. Then we switch the order of the multiplication on the right side, changing b * a to a * b. Now our assumption states that a <= a * b
  rw [one_mul, mul_comm] at h
  -- We have that a times b = a times b, so we can use reflexivity to prove the goal.
  exact h

-- Proof Statement: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right_train1 (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- b is either 0 or the successor of some natural number d.
  cases b with d
  -- a * 0 != 0 -> 0 != 0
  rw [mul_zero] at h
  -- 0 != 0 is false so the theorem doesn't hold for this case.
  tauto
  -- a <= a * succ d -> a <= a * d + a
  rw [mul_succ]
  -- a <= a * d + a ->  * d + a = a + a * d
  use a * d
  -- a * d + a = a + a * d -> a * d + a = a + a * d
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right_test (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- proof by induction on b
  induction b with d _
  -- for the base case, a * 0 != 0 -> 0 != 0
  apply mul_left_ne_zero at h
  -- 0 != 0 is false so the theorem doesn't hold for this case.
  tauto
  -- For the inductive step, we have a <= a * succ d -> a <= a * d + a by the definition of multiplication.
  rw [mul_succ]
  -- a <= a * d + a -> a * d + a = a + a * d by the definition of inequality, if we set a * d to be a.
  use a * d
  -- a * d + a = a + a * d -> a * d + a = a + a * d by the commutative property of addition.
  rw [add_comm]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
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
  -- If x equals 0, then x * y = 0, which implies that 0 = 1.
  rw [h0, zero_mul] at h
  -- 0 = 1 is false, so we can use this to show that x is not equal to 0.
  tauto
  -- We have shown that x = 1 which proves the goal.
  exact h1

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one_test (x y : ℕ) (h : x * y = 1) : x = 1 := by
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
  -- for the succ a = 0 case, succ a * y = 1 -> 0 * y = 1 -> 0 = 1
  rw [h0, zero_mul] at h
  -- 0 = 1 is false, so we can use this to show that x is not equal to 0.
  tauto
  -- for the succ a = 1 case, succ a = 1 -> 1 = 1
  rw [h1]
  -- 1 = 1 is true by reflexivity
  rfl

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one_train1 (x y : ℕ) (h : x * y = 1) : x = 1 := by
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
  -- 0 = 1 is false, so we can use this to show that x is not equal to 0.
  tauto
  -- We have shown that x = 1 which proves the goal.
  tauto

-- Proof Statement: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- We are given that a != 0. So, there exists a natural number 'n' such that 'a' equals 'n' plus 1, given that 'a' is not equal to zero.
  apply eq_succ_of_ne_zero at ha
  -- We are given that b != 0. So, there exists a natural number 'n' such that 'b' equals n plus 1, given that 'b' is not equal to zero.
  apply eq_succ_of_ne_zero at hb
  -- There exists a natural number 'c' such that 'a' is equal to the successor of 'c'.
  cases ha with c hc
  -- There exists a natural number 'd' such that 'b' is equal to the successor of 'd'.
  cases hb with d hd
  -- We substitute the variable 'a' with 'succ c' in the goal.
  rw [hc]
  -- We substitute the variable 'b' with 'succ d' in the goal.
  rw [hd]
  -- Rewrite the succ c * succ d as succ c * d + succ c.
  rw [mul_succ]
  -- Rewrite succ c * d + succ c as succ (succ c * d + c).
  rw [add_succ]
  -- flip the sides of the goal so that the new goal is 0 is not equal to succ (succ c * d + c)
  symm
  -- We know that 0 is not equal to the successor of any natural number, so we can use this to prove the goal.
  apply zero_ne_succ

-- Proof Statement: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem mul_ne_zero_train1 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
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
  -- succ (succ a * b + a) ≠ 0 -> 0 ≠ succ (succ a * b + a) by the symmetry property of inequality
  symm
  -- We know that 0 is not equal to the successor of any natural number, so we can use this to prove the goal.
  apply zero_ne_succ

-- Proof Statement: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem mul_ne_zero_test (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
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
  -- succ a * b + succ a ≠ 0 -> succ (succ a * b + a) ≠ 0
  rw [add_succ]
  -- succ (succ a * b + a) ≠ 0 -> 0 ≠ succ (succ a * b + a)
  symm
  -- We know that 0 is not equal to the successor of any natural number, so we can use this to prove the goal.
  apply zero_ne_succ

-- Proof Statement: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- We introduce a new fact stating that if neither a nor b is zero, then their product cannot be zero. This is derived from the fact that the product of two non-zero natural numbers is never zero.
  have h2 := mul_ne_zero a b
  -- We have shown that both a and b can't be non-zero so either a or b must be zero.
  tauto

-- Proof Statement: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem mul_eq_zero_train1 (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- We introduce a new fact stating that if neither a nor b is zero, then their product cannot be zero.
  have h2 := mul_ne_zero a b
  -- a * b ≠ 0 -> 0 -> a * b ≠ a * b by substituting that a * b = 0
  nth_rewrite 3 [← h] at h2
  -- a * b ≠ a * b is a contradiction, so either a = 0 or b = 0
  tauto

-- Proof Statement: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem mul_eq_zero_test (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- We introduce a new fact stating that if neither a nor b is zero, then their product cannot be zero.
  have h2 := mul_ne_zero a b
  -- a * b ≠ 0 -> 0 -> 0 ≠ 0
  rw [h] at h2
  -- 0 ≠ 0 is a contradiction, so either a = 0 or b = 0
  tauto

-- Proof Statement: Prove that if a times b is equal to a times c, then b is equal to c.
theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  -- Assume that b is a natural number and use induction on b. In the base case, b is 0. We also generalize over c, which means that we assume that c is an arbitrary but fixed natural number. Now, the goal is to show that 0 equals c given that a is a non-zero natural number and a times 0 equals a times c.
  induction b with d hd generalizing c
  -- We know that a * 0 = 0 so, 0 = a * c.
  rw [mul_zero] at h
  -- We flip the sides so that a * c = 0.
  symm at h
  -- We apply the fact that if a times b is equal to 0, then either a is equal to 0 or b is equal to 0.
  apply mul_eq_zero at h
  -- We consider the two possible cases for h: either a is equal to 0 or b is equal to 0.
  cases h with h1 h2
  -- If a is equal to 0, then we have a contradiction because we are given that a is not equal to 0.
  tauto
  -- If b is equal to 0, then we have that 0 = c.
  rw [h2]
  -- We have that 0 = 0 by substituting 0 for c, so we can use reflexivity to prove the goal.
  rfl
  -- We consider two subcases for c: when c is 0 and when c is a successor of another natural number e. For the first subcase, we need to show that the successor of d equals 0 given the hypothesis that a times the successor of d equals a times 0.
  cases c with e
  -- We know that a * succ d = a * 0, so a * d + a = 0, because for any natural numbers a and d, a * succ d = a * d + a and for any natural number a, a * 0 = 0.
  rw [mul_succ, mul_zero] at h
  -- We apply the fact that for any natural numbers a and b, if a + b = 0, then b = 0 to get that a = 0.
  apply add_left_eq_zero at h
  -- We have that a = 0, so we can use this to prove the goal.
  tauto
  -- Rewrite the equation a * succ d = a * succ e to a * d + a = a * e + a, using the theorem that multiplication of a natural number a with the successor of another natural number d (or e) is equal to the sum of a * d (or e) and a.
  rw [mul_succ, mul_succ] at h
  -- We use the fact that if two sums are equal and they both have the same term added to them, then the original sums before the addition must have been equal. This simplifies a * d + a = a * e + a to a * d = a * e.
  apply add_right_cancel at h
  -- We apply the induction hypothesis hd to the equation a * d = a * e which gives us d = e.
  apply hd at h
  -- We substitute e for d in the goal which gives us the new goal succ e = succ e.
  rw [h]
  -- The goal that succ e = succ e is true by reflexivity.
  rfl

-- Proof Statement: Prove that if a times b is equal to a times c, then b is equal to c.
theorem mul_left_cancel_train1 (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
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
  -- succ d = succ e -> succ e = succ d
  rw [h]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a times b is equal to a times c, then b is equal to c.
theorem mul_left_cancel_test (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
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
  -- a * d = a * e -> d = e
  apply hd at h
  -- succ d = succ e -> succ e = succ d
  rw [h]
  -- The LHS and RHS are equal, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  -- Rewrite the goal with the hypothesis a * b = a using the fact that a times 1 equals a.
  nth_rewrite 2 [← mul_one a] at h
  -- Apply the the theorem that states that for all natural numbers a and b, a times b is equal to a times c, then b is equal to c which shows that b = 1.
  exact mul_left_cancel a b 1 ha h

-- Proof Statement: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem mul_right_eq_self_train1 (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  -- Since b is a natural number, it is either 0 or the successor of some natural number.
  cases b with d hd
  -- if a = 0, then a * 0 = a -> 0 = a
  rw [mul_zero] at h
  -- 0 = a is a contradiction, so we don't need to consider this case.
  tauto
  -- if a is not equal to 0, then a * succ d = a -> a * succ d = a * 1
  nth_rewrite 2 [← mul_one a] at h
  -- by properties of multiplication, we know that this implication is true.
  exact mul_left_cancel a (succ d) 1 ha h

-- Proof Statement: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem mul_right_eq_test (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  --  a * b = a -> a * 1 * b = a * 1
  rw [← mul_one a] at h
  -- a * 1 * b = a * 1 -> a * (1 * b) = a * 1
  rw [mul_assoc] at h
  -- a * (1 * b) = a * 1 -> a * b = a * 1
  rw [one_mul b] at h
  -- Apply the the theorem that states that for all natural numbers a and b, a times b is equal to a times c, then b is equal to c which shows that b = 1.
  exact mul_left_cancel a b 1 ha h

end MyNat
