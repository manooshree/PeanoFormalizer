import Game.LevelsClean.MultiplicationClean
import Game.MyNat.Power

namespace MyNat

-- Proof Statement: Prove that 0 to the power of 0 is 1
theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  -- Rewrite the left-hand side of the equation using the theorem that any number to the power of 0 is 1
  rw [pow_zero]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl

theorem zero_pow_zero_dev_1 : (0 : ℕ) ^ 0 = 1 := by
  -- 1 = 1
  rw [pow_zero]
  -- lhs = rhs, so we are done.
  rfl

theorem zero_pow_zero_dev_2 : (0 : ℕ) ^ 0 = 1 := by
  -- We define the power operation such that a^0 = 1 for any natural number a, so we can write 0^0 = 1.
  rw [pow_zero]
  -- The goal we are left with is now to prove that 1 = 1, which is true by reflexivity
  rfl

-- Proof Statement: Prove that 0^(succ m) = 0
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number.
  rw [pow_succ]
  -- Rewrite the left hand side using the identity that any natural number multiplied by 0 is 0
  rw [mul_zero]
  -- The goal is now to prove that 0 = 0, which is true by reflexivity
  rfl

-- Proof Statement: Prove that 0^(succ m) = 0
theorem zero_pow_succ_dev_1 (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  -- 0^m * 0
  rw [pow_succ]
  -- 0=0
  rw [mul_zero]
  -- lhs = rhs, so we are done.
  rfl

-- Proof Statement: Prove that 0^(succ m) = 0
theorem zero_pow_succ_dev_2 (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  -- We can use induction on m. For the base case, we want to show that 0^succ(0) = 0.
  induction m with h hd
  -- Using the fact that 0 to the power of the successor of 1 is equal to 0 ^ 0 + 0.
  rw [pow_succ]
  -- We know that anything multiplied by 0 is equal to 0, so our goal becomes: 0 = 0
  rw [mul_zero]
  -- We can conclude the proof by reflexivity, as the LHS and RHS of our goal are identical.
  rfl
  -- Next, we consider the inductive case, where we want to show that 0^succ(succ m) = 0. By the successor definition of the power function, we can write our goal as: 0^succ(m) * 0 = 0.
  rw[pow_succ]
  -- We see that we can apply our inductive hypothesis, that 0^succ(m) = 0, and our goal becomes: 0*0 = 0
  rw[hd]
  -- Anything multiplied by zero is zero, so we simplify to: 0 = 0
  rw[mul_zero]
  -- The lhs and rhs are identical, so we are done by reflexivity.
  rfl

-- Proof Statement: Prove that a^1 = a
theorem pow_one (a : ℕ) : a ^ 1 = a  := by
  -- Rewrite the left hand side using the identity that 1 is equal to the successor of 0
  rw [one_eq_succ_zero]
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number.
  rw [pow_succ]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the left hand side using the identity that any natural number multiplied by 1 is equal to that natural number
  rw [one_mul]
  -- The goal is now to prove that a = a, which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^1 = a
theorem pow_one_dev_1 (a : ℕ) : a ^ 1 = a  := by
  -- a^succ(0) = a
  rw [one_eq_succ_zero]
  -- a^0 * a = a
  rw [pow_succ]
  -- 1 * a = a
  rw [pow_zero]
  -- a = a
  rw [one_mul]
  -- lhs = rhs, so we are done.
  rfl

-- Proof Statement: Prove that a^1 = a
theorem pow_one_dev_2 (a : ℕ) : a ^ 1 = a  := by
  -- Using the fact that we defined 1 to be the successor of zero, we can write this as: a^succ(0) = a.
  rw[one_eq_succ_zero]
  -- We defined the power function with the axiom such that for any natural numbers a,b, a^succ(b) = a^b * a. Using this, we can write our goal as: a^0 * a = a
  rw[pow_succ]
  -- Since anything to the power of zero is also zero, we can simplify our goal to: 1 * a = a
  rw[pow_zero]
  -- Once again, we can use the fact that 1 is the successor 0, to write: succ(0) * a = a
  rw[one_eq_succ_zero]
  -- Using the axioms with which we defined multiplication, namely the fact that for any natural numbers a,b, succ(b) * a = b* a + a, we can simplify to: 0 * a + a = a.
  rw[succ_mul]
  -- Since anything multiplied by zero is also zero, we simplify our goal to: 0 + a = a.
  rw[zero_mul]
  -- Since adding zero to any natural number does not change its, we can simplify our goal to: a=a.
  rw[zero_add]
  -- Since the LHS and RHS are prcisely the same expression, we are done by reflexivity.
  rfl

-- Proof Statement: Prove that 1^m = 1
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- Induct on m, with d = 0 as the base case and the inductive hypothesis 1^d = 1. There are now two proof goals, prove base case: 1^0 = 1 and inductive step: 1^d = 1 implies 1^(succ d) = 1.
  induction m with d hd
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number.
  rw [pow_succ]
  -- Rewrite the left hand side using the induction hypothesis
  rw [hd]
  -- Rewrite the left hand side using the identity that any natural number multiplied by 1 is equal to that natural number
  rw [mul_one]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl

-- Proof Statement: Prove that 1^m = 1
theorem one_pow_dev_1 (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- We can use induction on m, with the inductive hypothesis 1^m = 1. Our base is 1^0 = 1, and our inductive case is 1^succ(m) = 1.
  induction m with m hm
  -- Simplify base case to 1 = 1
  rw [pow_zero]
  -- rhs = lhs, so we are done.
  rfl
  -- Next, we consider the inductive case, which we write as 1^m * 1 = 1.
  rw [pow_succ]
  -- 1 * 1 = 1
  rw [hm]
  -- 1=1
  rw [mul_one]
  -- rhs = lhs, so we are done.
  rfl

-- Proof Statement: Prove that 1^m = 1
theorem one_pow_dev_2 (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- We can begin by inducting on m.
  induction m with h hd
  -- First, we prove the base case, which states that 1^0 = 1. To do so, we use the fact that anything to the power of zero is zero, so 1^0 = 1.
  rw[pow_zero]
  -- Thus, we have simplified our statement to 1=1, so our proof is complete by reflexivity.
  rfl
  -- Next, we can consider the inductive hypothesis, which states that 1^succ(h) = 1. To do so, we can induct on h again, with a variable k.
  induction h with k hk
  -- Our new base case is 1^succ(0) = 1. To prove this, we can begin by simplifying using the successor axiom for the power operation, so 1^succ(0) = 1^0*1, and our goal becomes 1^0 *1 = 1.
  rw [pow_succ]
  -- We can use the fact that anything to the power of zero is one, and simplify to: 1 * 1 =1.
  rw[pow_zero]
  -- Simplifying with the fact that multiplication by one is equivalent to the identity operation, we know that 1*1=1, and thus our goal state becomes 1=1.
  rw[mul_one]
  -- Finally, by reflexivity, we are done with the base case.
  rfl
  -- Next, we can consider the inductive case, which states that 1^succ(succ(k)) = 1. Using the successor axiom for powers, we can write our goal as: 1^succ(k) * 1 = 1.
  rw[pow_succ]
  -- We can simplify the LHS using the fact that multiplication by one is the identity operation, and get: 1^succ(k) = 1.
  rw[mul_one]
  -- Thus, we see that our goal state 1^succ(k) = 1 is precisely the same as our hypothesis hd, so we are done
  exact hd

-- Proof Statement: Prove that a^2 = a * a
theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  -- Rewrite the left hand side using the identity that 2 is equal to the successor of 1
  rw [two_eq_succ_one]
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number.
  rw [pow_succ]
  -- Rewrite the left hand side using the identity that any natural number to the power of 1 is equal to that natural number
  rw [pow_one]
  -- The goal is now to prove that a * a = a * a, which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^2 = a * a
theorem pow_two_dev_1 (a : ℕ) : a ^ 2 = a * a := by
  -- a^1* a = a*a
  rw [two_eq_succ_one, pow_succ]
  -- a^1* a = a*a
  rw [pow_one]
  -- lhs=rhs, so we are done.
  rfl

-- Proof Statement: Prove that a^2 = a * a
theorem pow_two_dev_2 (a : ℕ) : a ^ 2 = a * a := by
  -- First, we observe that two is the successor of one, and write our goal as: a^succ(1) = a*a.
  rw[two_eq_succ_one]
  -- We know that anything to the power of the successor of one is equal to that number multiplied by itself, so we can rewrite our goal as: a * a = a*a a
  rw[pow_succ, pow_one]
  -- LHS = RHS, so our proof is complete by the reflexive property of equality.
  rfl

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a^(m + d) = a^m * a^d. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + d) = a^m * a^d implies a^(m + succ d) = a^m * a^(succ d).
  induction n with d hd
  -- Rewrite the left hand side using the identity that the sum of any natural number and 0 is equal to that natural number
  rw [add_zero]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the right hand side using the identity that any natural number multiplied by 1 is equal to that natural number
  rw [mul_one]
  -- The goal is now to prove that a^m = a^m, which is true by reflexivity
  rfl
  -- Rewrite the left hand side using the identity that the sum of any natural number and the successor of another natural number is equal to the successor of the sum of the two natural numbers
  rw [add_succ]
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the right hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the left hand side using the induction hypothesis
  rw [hd]
  -- Rewrite the left hand side using the identity that any natural number multiplied by the product of two natural numbers is equal to the product of the first natural number multiplied by the second natural number multiplied by the third natural number
  rw [mul_assoc]
  -- The goal is now to prove that a^m * (a^d * a) = a^m * a^(d + 1), which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem pow_add_dev_1 (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- We can use induction on n, making the inductive hypothesis that a ^ (m + d) = a ^ m * a ^ d. Then, the base case is a ^ (m + 0) = a ^ m * a ^ 0, and the inductive case is: a ^ (m + succ d) = a ^ m * a ^ succ d
  induction n with d hd
  -- Simplify the base case to a^m = a^m * a^0
  rw [add_zero]
  -- a^m = a^m * 1
  rw [pow_zero]
  -- a^m = a^m
  rw [mul_one]
  -- lhs = rhs, so we are done with the base case.
  rfl
  -- For the inductive case we have to show that a ^ (m + succ d) = a ^ m * a ^ succ d, which can be simplified to a ^ succ (m + d) = a ^ m * a ^ succ d
  rw [add_succ]
  -- a ^ (m + d) * a = a ^ m * a ^ succ d
  rw [pow_succ]
  -- a ^ (m + d) * a = a ^ m * (a ^ d * a)
  rw [pow_succ]
  -- a ^ m * a ^ d * a = a ^ m * (a ^ d * a) by the inductive hypothesis
  rw [hd]
  -- a ^ m * (a ^ d * a) = a ^ m * (a ^ d * a)
  rw [mul_assoc]
  -- lhs = rhs, so we are done.
  rfl

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem pow_add_dev_2 (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with t = 0 as the base case and the inductive hypothesis a^(m + t) = a^m * a^t. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + t) = a^m * a^t implies a^(m + succ t) = a^m * a^(succ t).
  induction n with t ht
  -- Rewrite the goal by first simplifying the expression m + 0 to m, then simplifying a raised to the power of 0 to 1, and finally simplifying any number multiplied by 1 to the number itself. This results in the goal a^m = a^m.
  rw [add_zero, pow_zero, mul_one]
  -- The goal is now to prove that a^m = a^m, which is true by reflexivity
  rfl
  -- Rewrite the expression a^(m + succ t) as a^m * (a^t * a) using the fact that (m + succ t) is the same as (succ (m + t)), and that a raised to the power (succ (m + t)) is the same as (a^(m + t) * a). Also, use the inductive hypothesis that a^(m + t) is equivalent to a^m * a^t, and the fact that multiplication is associative
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc]
  -- The goal is now to prove that a^m * (a^d * a) = a^m * a^(d + 1), which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a * b)^n = a^n * b^n
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a * b)^d = a^d * b^d. There are now two proof goals, prove base case: (a * b)^0 = a^0 * b^0 and inductive step: (a * b)^d = a^d * b^d implies (a * b)^(succ d) = a^(succ d) * b^(succ d).
  induction n with d hd
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the right hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the right hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the right hand side using the identity that any natural number multiplied by 1 is equal to that natural number
  rw [mul_one]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the right hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the right hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the left hand side using the induction hypothesis
  rw [hd]
  -- Rearrange the multiplication in both sides of the equation to group them in a different order using the associative property of multiplication.
  repeat rw [mul_assoc]
  -- Rearrange the multiplication in the right-hand side of the equation, changing 'a * (b^d * b)' to 'b^d * b * a'
  rw [mul_comm a (_ * b)]
  -- Rewrite the right-hand side of the equation to move the multiplication of b and a inside the parentheses, changing b^d * b * a to b^d * (b * a).
  rw [mul_assoc]
  -- We rewrite the expression to swap the order of multiplication in b * a to a * b, since multiplication is commutative for natural numbers.
  rw [mul_comm b a]
  -- The goal is now to prove that a^d * (b^d * (a * b)) = a^d * (b^d * (a * b)), which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a * b)^n = a^n * b^n
theorem mul_pow_dev_1 (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
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
  -- a ^ d * (b ^ d * (a * b)) = a ^ d * (b ^ d * (b * a))
  rw [mul_assoc]
  -- a ^ d * (b ^ d * (a * b)) = a ^ d * (b ^ d * (a * b))
  rw [mul_comm b a]
  -- lhs = rhs, so we are done.
  rfl

-- Proof Statement: Prove that (a * b)^n = a^n * b^n
theorem mul_pow_dev_2 (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a * b)^d = a^d * b^d. There are now two proof goals, prove base case: (a * b)^0 = a^0 * b^0 and inductive step: (a * b)^d = a^d * b^d implies (a * b)^(succ d) = a^(succ d) * b^(succ d).
  induction n with t Ht
  -- Rewrite the left-hand side of the goal using the theorem that x^0 = 1, then simplify a^0 * b^0 to 1 * 1, and finally simplify 1 * 1 to 1
  rw [pow_zero, pow_zero, pow_zero, mul_one]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- We rewrite the goal using the property that (a * b)^(t+1) = (a * b)^t * (a * b). We use the inductive hypothesis that (a * b)^t = a^t * b^t.
  rw [pow_succ, pow_succ, pow_succ, Ht]
  -- Rewrite the left-hand side of the equation to move the multiplication of b and a inside the parentheses, changing b^d * b * a to b^d * (b * a).
  repeat rw [mul_assoc]
  -- Rearrange the terms on the right side of the equation using commutativity and associativity of multiplication. Specifically, swap a and (b * t), then regroup terms, and finally swap b and a.
  rw [mul_comm a (_ * b), mul_assoc, mul_comm b a]
  -- The goal is now to prove that a^t * (b^t * (a * b)) = a^t * (b^t * (a * b)), which is true by reflexivity
  rfl

-- Proof Statement: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a ^ m) ^ t = a ^ (m * t). There are now two proof goals, prove base case: (a ^ m) ^ 0 = a ^ (m * 0) and inductive step: (a ^ m) ^ t = a ^ (m * t) implies (a ^ m) ^ succ t = a ^ (m * succ t).
  induction n with t Ht
  -- Rewrite m * 0 to 0 in the right side
  rw [mul_zero]
  -- Rewrite (a ^ m) ^ 0 to 1 in the left side
  rw [pow_zero]
  -- Rewrite a ^ 0 to 1 in the right side
  rw [pow_zero]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- Rewrite the left-hand side using the theorem that states (x^n)^(succ t) = (x^n)^t * (x^n)
  rw [pow_succ]
  -- Use the induction hypothesis to replace (a^m)^t with a^(m*t)
  rw [Ht]
  -- Rewrite the right-hand side using the theorem that states m*(succ t) = m*t + m
  rw [mul_succ]
  -- Rewrite the right-hand side using the theorem that states x^(a+b) = x^a * x^b
  rw [pow_add]
  -- The goal is now to prove that a^(m\*t) * a^m = a^(m*t) * a^m, which is true by reflexivity
  rfl

-- Proof Statement: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem pow_pow_dev_1 (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with (a ^ m) ^ 0 = a ^ (m * 0) as the base case and (a ^ m) ^ succ t = a ^ (m * succ t) as the inductive case.
  induction n with t Ht
  -- 1 = 1
  rw [mul_zero, pow_zero, pow_zero]
  -- LHS = RHS
  rfl
  -- (a ^ m) ^ succ t = a ^ (m * succ t)
  rw [pow_succ, Ht, mul_succ, pow_add]
  -- LHS = RHS
  rfl

-- Proof Statement: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem pow_pow_dev_2 (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a ^ m) ^ t = a ^ (m * t).
  induction n with t Ht
  -- for the base case, simplify the LHS by the properties of powers and the RHS by the properties of multiplication to 1 = a ^ 0
  rw [pow_zero, mul_zero]
  -- further simplify the RHS by the properties of powers to 1 = 1
  rw [pow_zero]
  -- LHS = RHS, so we have shown the base case
  rfl
  -- simplify the LHS by the properties of powers to (a ^ m) ^ t * a ^ m = a ^ (m * succ t)
  rw [pow_succ]
  -- use the inductive hypothesis to simplify the LHS
  rw [Ht]
  -- simplify the LHS by the properties of multiplication and power to a ^ (m * t) * a ^ m = a ^ (m * t) * a ^ m
  rw[mul_succ, pow_add]
  -- LHS = RHS, so we complete the proof by induction
  rfl

-- Proof Statement: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- Rewrite (a + b)^2 as (a + b) * (a + b) using the theorem that x^2 = x * x
  rw [pow_two]
  -- Rewrite a^2 as a * a using the theorem that x^2 = x * x
  rw [pow_two]
  -- Rewrite b^2 as b * b using the theorem that x^2 = x * x
  rw [pow_two]
  -- Rearrange the terms on the right hand side of the equation, swapping the order of b * b and 2 * a * b using the commutative property of addition
  rw [add_right_comm]
  -- Use the distributive property of multiplication over addition to expand (a + b) * (a + b) to a * (a + b) + b * (a + b)
  rw [mul_add]
  -- Use the distributive property to expand a * (a + b) to a * a + a * b
  rw [add_mul]
  -- Use the distributive property to expand b * (a + b) to b * a + b * b
  rw [add_mul]
  -- Rewrite 2 * a * b as a * b + a * b using the theorem that 2 * x = x + x
  rw [two_mul]
  -- Use the distributive property to expand (a * b + a * b) to a * b + a * b
  rw [add_mul]
  -- Rewrite b * a as a * b using the commutative property of multiplication
  rw [mul_comm b a]
  -- Use the associative property of addition to rearrange a * a + a * b + (a * b + b * b) to a * a + a * b + a * b + b * b
  rw [← add_assoc]
  -- Use the associative property of addition again to rearrange a * a + (a * b + a * b) + b * b to a * a + a * b + a * b + b * b
  rw [← add_assoc]
  -- The goal is now to prove that a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b, which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem add_sq_dev_1 (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- (a + b) * (a + b) = a ^ 2 + b ^ 2 + 2 * a * b
  rw [pow_two]
  -- (a + b) * (a + b) = a * a + b ^ 2 + 2 * a * b
  rw [pow_two]
  -- (a + b) * (a + b) = a * a + b * b + 2 * a * b
  rw [pow_two]
  -- (a + b) * (a + b) = a * a + 2 * a * b + b * b
  rw [add_right_comm]
  -- (a + b) * a + (a + b) * b = a * a + 2 * a * b + b * b
  rw [mul_add]
  -- a * a + b * a + (a + b) * b = a * a + 2 * a * b + b * b
  rw [add_mul]
  -- a * a + b * a + (a * b + b * b) = a * a + 2 * a * b + b * b
  rw [add_mul]
  -- a * a + b * a + (a * b + b * b) = a * a + (a + a) * b + b * b
  rw [two_mul]
  -- a * a + b * a + (a * b + b * b) = a * a + (a * b + a * b) + b * b
  rw [add_mul]
  -- a * a + a * b + (a * b + b * b) = a * a + (a * b + a * b) + b * b
  rw [mul_comm b a]
  -- a * a + a * b + a * b + b * b = a * a + (a * b + a * b) + b * b
  rw [← add_assoc]
  -- a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b
  rw [← add_assoc]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem add_sq_dev_2 (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- Rewrite the expression for the square of (a + b), a^2, and b^2 to be (a + b) * (a + b), a * a, and b * b respectively.
  rw [pow_two, pow_two, pow_two]
  -- Rearrange the terms on the right hand side of the equation, swapping the order of b * b and 2 * a * b. This is based on the commutative property of addition, which states that the order of the terms does not change the result of the addition.
  rw [add_right_comm]
  -- rewrite the left-hand side of the equation using the distributive property of multiplication over addition. This expands (a + b) * (a + b) to a * a + b * a + a * b + b * b.
  rw [mul_add, add_mul, add_mul]
  -- Rewrite the term 2 * a * b in the goal as (a * b + a * b) using the theorem that 2 times a number is the same as the number added to itself. Also, rewrite the term a * b + b * b as (a * b + a * b) + b * b using the theorem that the product of a sum is the sum of the products.
  rw [two_mul, add_mul]
  -- We rewrite the expression a * b as b * a in the goal. This is based on the commutative property of multiplication, which states that the order of the factors does not change the product. This results in the new goal: a * a + a * b + (a * b + b * b) = a * a + (a * b + a * b) + b * b.
  rw [mul_comm b a]
  -- We use the theorem that states the associativity of addition twice to rearrange the left-hand side of the equation. This changes the goal to proving that a * a + a * b + a * b + b * b equals a * a + a * b + a * b + b * b.
  rw [← add_assoc, ← add_assoc]
  -- The goal is now to prove that a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b, which is true by reflexivity
  rfl

end MyNat
