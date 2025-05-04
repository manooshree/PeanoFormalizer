import Game.Levels.LessOrEqual
import Game.Levels.Multiplication
import Game.Levels.AdvMultiplication



namespace MyNat


-- Proof Statement: Prove that if a times b is not equal to 0, then b is not equal to 0.
theorem truncated_mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  -- We consider the case where the inequality a ≤ b can be expressed as b being equal to a plus some natural number d.
  cases h with d hd
  -- We use d * t as a specific natural number that can be used to rewrite a * t ≤ b * t as b * t = a * t + d * t.
  use d * t
  -- We know that b = a + d, so we can substitute b with a + d in the goal. Then rewrite the goal as a * t + d * t ≤ a * t + d * t by the distributive property of multiplication over addition.
  rw [hd, add_mul]

-- Proof Statement: Prove that if a is not equal to 0, then a is the successor of some natural number.
theorem truncated_mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Assume that b equals 0. The goal is now to show that this leads to a contradiction.
  intro hb
  -- We are given that a * b ≠ 0, the negation of this is a * b = 0, if we prove this we will have a contradiction.
  apply h

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem truncated_eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- We consider two cases for a: when a is zero and when a is the successor of another natural number.
  cases a with d
  -- By logical reasoning, we know that 0 cannot be equal to 0, which is a contradiction. Therefore, there is no natural number such that 0 is the successor of that number so we can close the case where a is 0.
  tauto
  -- We provide an example where the natural number 'd' satisfies the condition that 'succ d' equals 'succ n'.
  use d

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem truncated_one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- We use the previous lemma to express a as the successor of some natural number n since a is not equal to 0.
  apply eq_succ_of_ne_zero at ha
  -- Simplify the hypothesis to say that a is the successor of some natural number n.
  cases ha with n hn

-- Proof Statement: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem truncated_one_le_of_ne_zero1 (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- sing the fact that 'a' is not zero, we express 'a' as the successor of some natural number 'n'.
  apply eq_succ_of_ne_zero at ha
  -- Simplify the hypothesis to say that a is the successor of some natural number n.
  cases ha with n hn
  -- 1 <= a means that there exists some natural number m such that 1 + m = a. We use n as the natural number m.
  use n

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem truncated_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- We are given that the product of a and b is not zero. Therefore, we can conclude that b is not zero.
  apply mul_left_ne_zero at h
  -- We showed that b is not zero, so we can use this to show that b is at least 1.
  apply one_le_of_ne_zero at h

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem truncated_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
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

-- Proof Statement: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem truncated_mul_right_eq_one1 (x y : ℕ) (h : x * y = 1) : x = 1 := by
    -- assume that x * y is not equal to 0
  have h2 : x * y ≠ 0
  -- rewrite the goal with the previous assumption so the new goal is 1 is not equal to 0
  rw [h]

-- Proof Statement: Prove that if a is not equal to 0 and b is not equal to 0, then a times b is not equal to 0.
theorem truncated_mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- We are given that a != 0. So, there exists a natural number 'n' such that 'a' equals 'n' plus 1, given that 'a' is not equal to zero.
  apply eq_succ_of_ne_zero at ha
  -- We are given that b != 0. So, there exists a natural number 'n' such that 'b' equals n plus 1, given that 'b' is not equal to zero.
  apply eq_succ_of_ne_zero at hb
  -- There exists a natural number 'c' such that 'a' is equal to the successor of 'c'.
  cases ha with c hc
  -- There exists a natural number 'd' such that 'b' is equal to the successor of 'd'.
  cases hb with d hd

-- Proof Statement: Prove that if a times b is equal to 0, then a is equal to 0 or b is equal to 0.
theorem truncated_mul_ne_zero1 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- We are given that a != 0. So, there exists a natural number 'n' such that 'a' equals 'n' plus 1, given that 'a' is not equal to zero.
  apply eq_succ_of_ne_zero at ha
  -- We are given that b != 0. So, there exists a natural number 'n' such that 'b' equals n plus 1, given that 'b' is not equal to zero.
  apply eq_succ_of_ne_zero at hb
  -- There exists a natural number 'c' such that 'a' is equal to the successor of 'c'.
  cases ha with c hc
  -- There exists a natural number 'd' such that 'b' is equal to the successor of 'd'.
  cases hb with d hd
  -- We substitute the variable 'a' with 'succ c' and 'b' with 'succ d' in the goal.
  rw [hc, hd]
  -- Rewrite the succ c * succ d as succ c * d + succ c. Also, rewrite succ c * d + succ c as succ (succ c * d + c). The goal now is to prove that succ (succ c * d + c) is not equal to zero.
  rw [mul_succ, add_succ]
  -- flip the sides of the goal so that the new goal is 0 is not equal to succ (succ c * d + c)
  symm


-- Proof Statement: Prove that if a is not equal to 0 and a times b equals a, then b equals 1.
theorem truncated_mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
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
  · tauto
  -- If b is equal to 0, then we have that 0 = c.
  · rw [h2]
    -- We have that 0 = 0 by substituting 0 for c, so we can use reflexivity to prove the goal.
    rfl
  -- We consider two subcases for c: when c is 0 and when c is a successor of another natural number e. For the first subcase, we need to show that the successor of d equals 0 given the hypothesis that a times the successor of d equals a times 0.
  cases c with e

theorem truncated_mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  -- Rewrite the goal with the hypothesis a * b = a using the fact that a times 1 equals a.
  nth_rewrite 2 [← mul_one a] at h
  -- Apply the the theorem that states that for all natural numbers a and b, a times b is equal to a times c, then b is equal to c which shows that b = 1.
  exact mul_left_cancel a b 1 ha h


-- Truncated Theorems Report:

-- truncated_mul_le_mul_right: 3 steps kept

-- truncated_mul_left_ne_zero: 2 steps kept

-- truncated_eq_succ_of_ne_zero: 3 steps kept

-- truncated_one_le_of_ne_zero: 2 steps kept

-- truncated_one_le_of_ne_zero1: 3 steps kept

-- truncated_le_mul_right: 2 steps kept

-- truncated_mul_right_eq_one: 8 steps kept

-- truncated_mul_right_eq_one1: 2 steps kept

-- truncated_mul_ne_zero: 4 steps kept

-- truncated_mul_ne_zero1: 7 steps kept

-- truncated_mul_left_cancel: 7 steps kept

-- truncated_mul_right_eq_self: 2 steps kept
