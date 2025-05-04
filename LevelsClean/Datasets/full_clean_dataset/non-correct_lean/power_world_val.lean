import Game.LevelsClean.MultiplicationClean
import Game.MyNat.Power

namespace MyNat


-- Theorem Declaration:
theorem zero_pow_zero_persona2 : (0 : ℕ) ^ 0 = 1 := by
  -- 1 = 1
  rw [pow_zero]

-- Theorem Declaration:
theorem zero_pow_zero_persona3 : (0 : ℕ) ^ 0 = 1 := by
  -- We define the power operation such that a^0 = 1 for any natural number a, so we can write 0^0 = 1.
  rw [pow_zero]

-- Theorem Declaration:
theorem zero_pow_succ_persona2 (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  -- We know that 0^(succ m) = 0^m * 0, so our goal becomes 0^m * 0 = 0
  rw [pow_succ]
  -- lhs = rhs, so we are done.
  rfl

-- Theorem Declaration:
theorem zero_pow_succ_persona3 (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  -- We can use induction on m. For the base case, we want to show that 0^succ(0) = 0.
  induction m with h hd
  -- Anything multiplied by zero is zero, so we simplify to: 0*0
  rw[mul_zero]
  -- The lhs and rhs are identical, so we are done by reflexivity.
  rfl

-- Theorem Declaration:
theorem pow_one_persona2 (a : ℕ) : a ^ 1 = a  := by
  -- a^succ(0) = a
  rw [one_eq_succ_zero]
  -- 1 * a = a
  rw [pow_zero]
  -- a = a
  rw [one_mul]
  -- lhs = rhs, so we are done.
  rfl

-- Theorem Declaration:
theorem pow_one_persona3 (a : ℕ) : a ^ 1 = a  := by
  -- Using the fact that we defined 1 to be the successor of zero, we can write this as: a^succ(0) = a.
  rw[one_eq_succ_zero]
  -- We defined the power function with the axiom such that for any natural numbers a,b, a^succ(b) = a^b * a. Using this, we can write our goal as: a^0 * a = a
  rw[pow_succ]
  -- Since anything to the power of zero is also zero, we can simplify our goal to: 1 * a = a
  rw[pow_zero]
  -- Once again, we can use the fact that 1 is the successor 0, to write: succ(0) * a = a
  rw[one_eq_succ_zero]
  -- Since anything multiplied by zero is also zero, we simplify our goal to: 0 + a = a.
  rw[zero_mul]
  -- Since adding zero to any natural number does not change its, we can simplify our goal to: a=a.
  rw[zero_add]
  -- Since the LHS and RHS are prcisely the same expression, we are done by reflexivity.
  rfl

-- Theorem Declaration:
theorem one_pow_persona2 (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- We can use induction on m, with the inductive hypothesis 1^m = 1. Our base is 1^0 = 1, and our inductive case is 1^succ(m) = 1.
  induction m with m hm
  -- We start with the base cae, which becomes 1 = 1
  rw [pow_zero]
  -- rhs = lhs, so we are done.
  rfl
  -- Next, we consider the inductive case, which we write as 1^m * 1 = 1.
  rw [pow_succ]
  -- 1 * 1 = 1
  rw [hm]
  -- rhs = lhs, so we are done.
  rfl

-- Theorem Declaration:
theorem one_pow_persona3 (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- We can begin by inducting on m.
  induction m with h hd
  -- First, we prove the base case, which states that 1^0 = 1. To do so, we use the fact that anything to the power of zero is zero, so 1^0 = 1.
  rw[pow_zero]
  -- Thus, we have simplified our statement to 1=1, so our proof is complete by reflexivity.
  rfl
  -- Next, we can consider the inductive hypothesis, which states that 1^succ(h) = 1. To do so, we can induct on h again, with a variable k.
  induction h with k hk
  -- Our new base case is 1^succ(0) = 1. To prove this, we can begin by simplifying using the successor axiom for the power operation, so 1^succ(0) = 1^0*1, and our goal becomes 1^0 *1 = 1.
  rw[pow_succ]
  -- We can use the fact that anything to the power of zero is zero, and simplify to: 1 * 1 =1.
  rw[pow_zero]
  -- Simplifying with the fact that multiplication by one is equivalent to the identity operation, we know that 1*1=1, and thus our goal state becomes 1=1.
  rw[mul_one]
  -- Next, we can consider the inductive case, which states that 1^succ(succ(k)) = 1. Using the successor axiom for powers, we can write our goal as: 1^succ(k) * 1 = 1.
  rw[pow_succ]
  -- We can simplify the LHS using the fact that multiplication by one is the identity operation, and get: 1^succ(k) = 1.
  rw[mul_one]
  -- Thus, we see that our goal state 1^succ(k) = 1 is precisely the same as our hypothesis hk, so we are done.
  exact hk

-- Theorem Declaration:
theorem pow_two_persona2 (a : ℕ) : a ^ 2 = a * a := by
  -- a^succ(1) = a*a
  rw [two_eq_succ_one]
  -- a^1* a = a*a
  rw [pow_succ]
  -- lhs=rhs, so we are done.
  rfl

-- Theorem Declaration:
theorem pow_two_persona3 (a : ℕ) : a ^ 2 = a * a := by
  -- First, we observe that two is the successor of one, and write our goal as: a^succ(1) = a*a.
  rw[two_eq_succ_one]
  -- Then, we can use the definition of the successor as adding one, namely succ(1) = 1+1, to write our goal as: a^(1+1) = a*a.
  rw[succ_eq_add_one]
  -- Then, we can use the additive property of the power function, and see that: a^1 * a^1 = a*a.
  rw[pow_add]
  -- LHS = RHS, so our proof is complete by the reflexive property of equality.
  rfl

-- Theorem Declaration:
theorem pow_add_persona2 (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- We can use induction on n, making the inductive hypothesis that a ^ (m + d) = a ^ m * a ^ d. Then, the base case is a ^ (m + 0) = a ^ m * a ^ 0, and the inductive case is: a ^ (m + succ d) = a ^ m * a ^ succ d
  induction n with d hd
  -- For the base case a ^ (m + 0) = a ^ m * a ^ 0 becomes a^m = a^m * a^0
  rw [add_zero]
  -- a^m = a^m * 1
  rw [pow_zero]
  -- a^m = a^m
  rw [mul_one]
  -- lhs = rhs, so we are done with the base case.
  rfl
  -- For the inductive case a ^ (m + succ d) = a ^ m * a ^ succ d, we begin by rewriting as a ^ succ (m + d) = a ^ m * a ^ succ d
  rw [add_succ]
  -- a ^ (m + d) * a = a ^ m * a ^ succ d
  rw [pow_succ]
  -- We use the inductive hypothesis hd, to get: a ^ m * a ^ d * a = a ^ m * (a ^ d * a)
  rw [hd]
  -- a ^ m * (a ^ d * a) = a ^ m * (a ^ d * a)
  rw [mul_assoc]
  -- lhs = rhs, so we are done.
  rfl

-- Theorem Declaration: Prove that a^(m + n) = a^m * a^n
theorem pow_add_persona3 (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a^(m + d) = a^m * a^d. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + d) = a^m * a^d implies a^(m + succ d) = a^m * a^(succ d).
  induction n with t ht
  -- Rewrite the goal by first simplifying the expression m + 0 to m, then simplifying a raised to the power of 0 to 1, and finally simplifying any number multiplied by 1 to the number itself. This results in the goal a^m = a^m.
  rw [add_zero, pow_zero, mul_one]
  -- Rewrite the expression a^(m + succ t) as a^m * (a^t * a) using the fact that (m + succ t) is the same as (succ (m + t)), and that a raised to the power (succ (m + t)) is the same as (a^(m + t) * a). Also, use the inductive hypothesis that a^(m + t) is equivalent to a^m * a^t, and the fact that multiplication is associative
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc]
  -- The goal is now to prove that a^m * (a^d * a) = a^m * a^(d + 1), which is true by reflexivity
  rfl

-- Theorem Declaration:
theorem mul_pow_persona2 (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- We can use induction on n. We begin with the base case, which is: 1 = a ^ 0 * b ^ 0
  induction n with d hd
  --1 = a ^ 0 * b ^ 0
  rw [pow_zero]
  -- 1 = 1 * b^0
  rw [pow_zero]
  -- 1 = 1*1
  rw [pow_zero]
  -- 1=1
  rw [mul_one]
  -- lhs = rhs, so we have proven the base case.
  rfl
  -- Next, we proceed with the inductive case, which states that: (a * b) ^ succ d = a ^ succ d * b ^ succ d. Thus becomes: (a * b) ^ d * (a * b) = a ^ succ d * b ^ succ d
  rw [pow_succ]
  -- (a * b) ^ d * (a * b) = a ^ d * a * b ^ succ d
  rw [pow_succ]
  -- (a * b) ^ d * (a * b) = a ^ d * a * (b ^ d * b)
  rw [pow_succ]
  -- With the inductive hypothesis hd, we get: a ^ d * b ^ d * (a * b) = a ^ d * a * (b ^ d * b)
  rw [hd]
  -- a ^ d * (b ^ d * (a * b)) = a ^ d * (a * (b ^ d * b))
  repeat rw [mul_assoc]
  -- a ^ d * (b ^ d * (a * b)) = a ^ d * (b ^ d * b * a)
  rw [mul_comm a (_ * b)]
  -- a ^ d * (b ^ d * (a * b)) = a ^ d * (b ^ d * (a * b))
  rw [mul_comm b a]
  -- lhs = rhs, so we are done.
  rfl

-- Theorem Declaration: Prove that (a * b)^n = a^n * b^n
theorem mul_pow_persona3 (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a * b)^d = a^d * b^d. There are now two proof goals, prove base case: (a * b)^0 = a^0 * b^0 and inductive step: (a * b)^d = a^d * b^d implies (a * b)^(succ d) = a^(succ d) * b^(succ d).
  induction n with t Ht
  -- Rewrite the left-hand side of the goal using the theorem that x^0 = 1, then simplify a^0 * b^0 to 1 * 1, and finally simplify 1 * 1 to 1
  rw [pow_zero, pow_zero, pow_zero, mul_one]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- We rewrite the goal using the property that (a * b)^(t+1) = (a * b)^t * (a * b). We use the inductive hypothesis that (a * b)^t = a^t * b^t.
  rw [pow_succ, pow_succ, pow_succ, Ht]
  -- Rearrange the terms on the right side of the equation using commutativity and associativity of multiplication. Specifically, swap a and (b * t), then regroup terms, and finally swap b and a.
  rw [mul_comm a (_ * b), mul_assoc, mul_comm b a]
  -- The goal is now to prove that a^d * (b^d * (a * b)) = a^d * (b^d * (a * b)), which is true by reflexivity
  rfl

-- Theorem Declaration: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem pow_pow_persona2 (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with (a ^ m) ^ 0 = a ^ (m * 0) as the base case and (a ^ m) ^ succ t = a ^ (m * succ t) as the inductive case.
  induction n with t Ht
  -- (a ^ m) ^ 0 = a ^ (m * 0) -> 1 = 1
  rw [mul_zero, pow_zero, pow_zero]
  -- LHS = RHS
  rfl
  -- LHS = RHS
  rfl

-- Theorem Declaration: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem pow_pow_persona3 (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a ^ m) ^ t = a ^ (m * t).
  induction n with t Ht
  -- for the base case, simplify the LHS by the properties of powers and the RHS by the properties of multiplication to 1 = a ^ 0
  rw [pow_zero, mul_zero]
  -- further simplify the RHS by the properties of powers to 1 = 1
  rw [pow_zero]
  -- LHS = RHS, so we have shown the base case
  rfl
  -- use the inductive hypothesis to simplify the LHS
  rw [Ht]
  -- simplify the LHS by the properties of multiplication and power to a ^ (m * t) * a ^ m = a ^ (m * t) * a ^ m
  rw[mul_succ, pow_add]
  -- LHS = RHS, so we complete the proof by induction
  rfl

-- Theorem Declaration:
theorem add_sq_persona2 (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- (a + b) * (a + b) = a^2 + b^2 + 2a*b
  rw [pow_two]
  -- (a + b) * (a + b) = a*a + b^2 + 2a*b
  rw [pow_two]
  -- (a + b) * (a + b) = a*a + b*b + 2a*b
  rw [pow_two]
  -- (a + b) * (a + b) = a*a + 2a*b + b*b
  rw [add_right_comm]
  -- a * (a + b) + b * (a + b) = a*a + 2a*b + b*b
  rw [mul_add]
  -- a * a + a * b + b * (a + b) = a*a + 2a*b + b*b
  rw [add_mul]
  -- a * a + a * b + b * a + b*b = a*a + 2a*b + b*b
  rw [add_mul]
  -- a * a + a * b + b * a + b*b = a*a + (a+a)*b + b*b
  rw [two_mul]
  -- a * a + a * b + (b * a + b*b) = a*a + (a*b + a*b) + b*b
  rw [add_mul]
  -- a * a + a * b + (a * b + b*b) = a*a + a*b + a*b + b*b
  rw [mul_comm b a]
  -- a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b
  rw [← add_assoc]
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem add_sq2_persona3 (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- Rewrite the expression for the square of (a + b), a^2, and b^2 to be (a + b) * (a + b), a * a, and b * b respectively.
  rw [pow_two, pow_two, pow_two]
  -- Rearrange the terms on the right hand side of the equation, swapping the order of b * b and 2 * a * b. This is based on the commutative property of addition, which states that the order of the terms does not change the result of the addition.
  rw [add_right_comm]
  -- rewrite the left-hand side of the equation using the distributive property of multiplication over addition. This expands (a + b) * (a + b) to a * a + b * a + a * b + b * b.
  rw [mul_add, add_mul, add_mul]
  -- We rewrite the expression a * b as b * a in the goal. This is based on the commutative property of multiplication, which states that the order of the factors does not change the product. This results in the new goal: a * a + a * b + (a * b + b * b) = a * a + (a * b + a * b) + b * b.
  rw [mul_comm b a]
  -- We use the theorem that states the associativity of addition twice to rearrange the left-hand side of the equation. This changes the goal to proving that a * a + a * b + a * b + b * b equals a * a + a * b + a * b + b * b.
  rw [← add_assoc, ← add_assoc]
  -- The goal is now to prove that a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b, which is true by reflexivity
  rfl

end MyNat
