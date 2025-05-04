import Game.Levels.Multiplication
import Game.MyNat.Power

World "Power"
Level 1
Title "zero_pow_zero"

namespace MyNat

/--
  `Pow a b`, with notation `a ^ b`, is the usual
  exponentiation of natural numbers. Internally it is
  defined via two axioms:

  * `pow_zero a : a ^ 0 = 1`

  * `pow_succ a b : a ^ succ b = a ^ b * a`

Note in particular that `0 ^ 0 = 1`.
-/
DefinitionDoc Pow as "^"

NewDefinition Pow

/--
`pow_zero a : a ^ 0 = 1` is one of the two axioms
defining exponentiation in this game.
-/
TheoremDoc MyNat.pow_zero as "pow_zero" in "^"

NewTheorem MyNat.pow_zero

/--
`pow_zero a : a ^ 0 = 1` is one of the two axioms
defining exponentiation in this game.
-/
TheoremDoc MyNat.pow_zero as "pow_zero" in "^"


-- Proof Statement: Prove that 0 to the power of 0 is 1
theorem skipped_zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  -- Rewrite the left-hand side of the equation using the theorem that any number to the power of 0 is 1
  rw [pow_zero]


-- Proof Statement: Prove that a^1 = a
theorem skipped_pow_one (a : ℕ) : a ^ 1 = a  := by
  -- Rewrite the left hand side using the identity that 1 is equal to the successor of 0
  rw [one_eq_succ_zero]
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number.
  rw [pow_succ]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- The goal is now to prove that a = a, which is true by reflexivity
  rfl -- error

-- Proof Statement: Prove that 1^m = 1
theorem skipped_one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  -- Induct on m, with d = 0 as the base case and the inductive hypothesis 1^d = 1. There are now two proof goals, prove base case: 1^0 = 1 and inductive step: 1^d = 1 implies 1^(succ d) = 1.
  induction m with d hd
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^2 = a * a
theorem skipped_pow_two (a : ℕ) : a ^ 2 = a * a := by
  -- Rewrite the left hand side using the identity that 2 is equal to the successor of 1
  rw [two_eq_succ_one]
  -- Rewrite the left hand side using the identity that any natural number to the power of 1 is equal to that natural number
  rw [pow_one] -- error
  -- The goal is now to prove that a * a = a * a, which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem skipped_pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a^(m + d) = a^m * a^d. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + d) = a^m * a^d implies a^(m + succ d) = a^m * a^(succ d).
  induction n with d hd
  -- Rewrite the left hand side using the identity that the sum of any natural number and 0 is equal to that natural number
  rw [add_zero]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ] -- error
  -- Rewrite the left hand side using the identity that any natural number raised to the power of the successor of another natural number is equal to that number raised to the power of the other number, multiplied by the original number
  rw [pow_succ]
  -- Rewrite the left hand side using the induction hypothesis
  rw [hd]
  -- Rewrite the left hand side using the identity that any natural number multiplied by the product of two natural numbers is equal to the product of the first natural number multiplied by the second natural number multiplied by the third natural number
  rw [mul_assoc]
  -- The goal is now to prove that a^m * (a^d * a) = a^m * a^(d + 1), which is true by reflexivity
  rfl

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem skipped_pow_add1 (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a^(m + d) = a^m * a^d. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + d) = a^m * a^d implies a^(m + succ d) = a^m * a^(succ d).
  induction n with t ht
  -- Rewrite the expression a^(m + succ t) as a^m * (a^t * a) using the fact that (m + succ t) is the same as (succ (m + t)), and that a raised to the power (succ (m + t)) is the same as (a^(m + t) * a). Also, use the inductive hypothesis that a^(m + t) is equivalent to a^m * a^t, and the fact that multiplication is associative
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc] -- error
  -- The goal is now to prove that a^m * (a^d * a) = a^m * a^(d + 1), which is true by reflexivity
  rfl


-- Proof Statement: Prove that (a * b)^n = a^n * b^n
theorem skipped_mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a * b)^d = a^d * b^d. There are now two proof goals, prove base case: (a * b)^0 = a^0 * b^0 and inductive step: (a * b)^d = a^d * b^d implies (a * b)^(succ d) = a^(succ d) * b^(succ d).
  induction n with d hd
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
  rw [pow_zero]
  -- Rewrite the left hand side using the identity that any natural number multiplied by 1 is equal to that natural number
  rw [mul_one]
  -- The goal is now to prove that 1 = 1, which is true by reflexivity
  rfl
  -- We rewrite the expression to swap the order of multiplication in b * a to a * b, since multiplication is commutative for natural numbers.
  rw [mul_comm b a] -- error
  -- The goal is now to prove that a^d * (b^d * (a * b)) = a^d * (b^d * (a * b)), which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a * b)^n = a^n * b^n
theorem skipped_mul_pow1 (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a * b)^d = a^d * b^d. There are now two proof goals, prove base case: (a * b)^0 = a^0 * b^0 and inductive step: (a * b)^d = a^d * b^d implies (a * b)^(succ d) = a^(succ d) * b^(succ d).
  induction n with t Ht
  -- Rewrite the left-hand side of the goal using the theorem that x^0 = 1, then simplify a^0 * b^0 to 1 * 1, and finally simplify 1 * 1 to 1
  rw [pow_zero, pow_zero, pow_zero, mul_one]
  -- We rewrite the goal using the property that (a * b)^(t+1) = (a * b)^t * (a * b). We use the inductive hypothesis that (a * b)^t = a^t * b^t.
  rw [pow_succ, pow_succ, pow_succ, Ht] -- error
  -- Rewrite the right-hand side of the equation to move the multiplication of b and a inside the parentheses, changing b^d * b * a to b^d * (b * a).
  repeat rw [mul_assoc]
  -- Rearrange the terms on the right side of the equation using commutativity and associativity of multiplication. Specifically, swap a and (b * t), then regroup terms, and finally swap b and a.
  rw [mul_comm a (_ * b), mul_assoc, mul_comm b a]
  -- The goal is now to prove that a^d * (b^d * (a * b)) = a^d * (b^d * (a * b)), which is true by reflexivity
  rfl

-- Proof Statement: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem skipped_pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a ^ m) ^ t = a ^ (m * t). There are now two proof goals, prove base case: (a ^ m) ^ 0 = a ^ (m * 0) and inductive step: (a ^ m) ^ t = a ^ (m * t) implies (a ^ m) ^ succ t = a ^ (m * succ t).
  induction n with t Ht
  -- Rewrite m * 0 to 0 in the right side
  rw [mul_zero]
  -- Rewrite (a ^ m) ^ 0 to 1 in the left side
  rw [pow_zero]
  -- The goal is now to prove that a^(m\*t) * a^m = a^(m*t) * a^m, which is true by reflexivity
  rfl -- error

-- Proof Statement: Prove that any natural number to the power of the power of another natural number is equal to that natural number to the power of the first natural number, multiplied by that natural number to the power of the second natural number
theorem skipped_pow_pow2 (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis (a ^ m) ^ t = a ^ (m * t). There are now two proof goals, prove base case: (a ^ m) ^ 0 = a ^ (m * 0) and inductive step: (a ^ m) ^ t = a ^ (m * t) implies (a ^ m) ^ succ t = a ^ (m * succ t).
  induction n with t Ht
  -- Rewrite the left-hand side of the goal using the theorem that states (x^n)^(succ t) = (x^n)^t * (x^n). Then, use the induction hypothesis to replace (a^m)^t with a^(m⋆t). Next, rewrite the right-hand side of the goal using the theorem that states m*(succ t) = m\*t + m. Finally, rewrite the right-hand side again using the theorem that states x^(a+b) = x^a * x^b. This simplifies the goal to proving that a^(m\*t) * a^m is equal to a^(m*t) * a^m.
  rw [pow_succ, Ht, mul_succ, pow_add] -- error
  -- The goal is now to prove that a^(m\*t) * a^m = a^(m*t) * a^m, which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem skipped_add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- Rewrite (a + b)^2 as (a + b) * (a + b) using the theorem that x^2 = x * x
  rw [pow_two] -- error
  -- Rewrite a^2 as a * a using the theorem that x^2 = x * x
  rw [pow_two]
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
  -- Use the associative property of addition to rearrange (a * a + a * b) + (a * b + b * b) to a * a + (a * b + (a * b + b * b))
  rw [← add_assoc]
  -- Use the associative property of addition again to rearrange a * a + (a * b + (a * b + b * b)) to a * a + a * b + (a * b + b * b)
  rw [← add_assoc]
  -- The goal is now to prove that a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b, which is true by reflexivity
  rfl

-- Proof Statement: Prove that (a + b)^2 = a^2 + b^2 + 2 * a * b
theorem skipped_add_sq2 (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  -- Rewrite the expression for the square of (a + b), a^2, and b^2 to be (a + b) * (a + b), a * a, and b * b respectively.
  rw [pow_two, pow_two, pow_two] -- error
  -- Rearrange the terms on the right hand side of the equation, swapping the order of b * b and 2 * a * b. This is based on the commutative property of addition, which states that the order of the terms does not change the result of the addition.
  rw [add_right_comm]
  -- rewrite the left-hand side of the equation using the distributive property of multiplication over addition. This expands (a + b) * (a + b) to a * a + b * a + a * b + b * b.
  rw [mul_add, add_mul, add_mul]
  -- We use the theorem that states the associativity of addition twice to rearrange the left-hand side of the equation. This changes the goal to proving that a * a + a * b + a * b + b * b equals a * a + a * b + a * b + b * b.
  rw [← add_assoc, ← add_assoc]
  -- The goal is now to prove that a * a + a * b + a * b + b * b = a * a + a * b + a * b + b * b, which is true by reflexivity
  rfl

end MyNat



-- Skipped Steps Theorems Report:

-- skipped_zero_pow_zero: 2 steps skipped

-- skipped_pow_one: 1 steps skipped

-- skipped_one_pow: 4 steps skipped

-- skipped_pow_two: 1 steps skipped

-- skipped_pow_add: 3 steps skipped

-- skipped_pow_add1: 2 steps skipped

-- skipped_mul_pow: 7 steps skipped

-- skipped_mul_pow1: 1 steps skipped

-- skipped_pow_pow: 6 steps skipped

-- skipped_pow_pow2: 2 steps skipped

-- skipped_add_sq: 3 steps skipped

-- skipped_add_sq2: 2 steps skipped
