import Game.Levels.Addition
import Game.MyNat.Multiplication
import Game.MyNat.PeanoAxioms
import Game.Levels.Multiplication

namespace MyNat


-- Proof Statement: Prove that 0 * m = m for all natural numbers
theorem truncated_mul_one (m : ℕ) : m * 1 = m := by
  -- Rewrite 1 as succ 0, using the axiom that succ 0 = 1
  rw [one_eq_succ_zero]
  -- Rewrite LHS m * succ 0 to m * 0 + m using the definition of multiplication with a successor.
  rw [mul_succ]
  -- Simplify m * 0 + m to 0 + m on LHS
  rw [mul_zero]

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem truncated_zero_mul (m : ℕ) : 0 * m = 0 := by
-- Perform induction on m, with d = 0 as the base case and the inductive hypothesis 0 * d = 0. There are now two proof goals, prove base case: 0 * 0 = 0, and inductive step: 0 * succ (d) = 0
  induction m with d hd
  -- First prove base case. Simplify LHS 0 * 0 to 0
  rw [mul_zero]
    -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- Now prove inductive step. Rewrite LHS 0 * succ (d) to 0 * d + 0, using the definition of multiplication
  rw [mul_succ]
    -- Simplify the LHS 0 * d + 0 to 0 + 0 using the inductive hypothesis
  rw [hd]
    -- Simplify the LHS o 0 + 0 to 0
  rw [add_zero]

-- Proof Statement: Prove that multiplication is commutative, that is a * b  = b * a for all natural numbers
theorem truncated_succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd
  -- First we prove base case. Simplify the LHS from succ a * 0 to 0
  rw [mul_zero]
  -- Simplify LHS a * 0 = 0
  rw [mul_zero]

  -- Proof Statement: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem truncated_mul_comm (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a. There are now two proof goals, prove base case: a * 0 = 0 * a, and inductive step: a * succ d = succ d * a.
  induction b with d hd
  -- First we prove base case. Simplify RHS 0 * a to 0
  rw [zero_mul]
  -- Simplify LHS a * 0 to 0
  rw [mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem truncated_mul_comm_2 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: a * 0 = 0 * a.
  rw [mul_zero]  -- Simplify LHS a * 0 to 0.
  rw [zero_mul]  -- Simplify RHS 0 * a to 0.

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem truncated_one_mul (m : ℕ): 1 * m = m := by
  -- Apply the commutative property of multiplication to rewrite LHS from 1 * m to m * 1
  rw [mul_comm]
  -- Simplify m * 1 to m
  rw [mul_one]

-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem truncated_two_mul (m : ℕ): 2 * m = m + m := by
  -- Rewrite 2 as succ(1), changing LHS from 2 * m to succ 1 * m
  rw [two_eq_succ_one]
  -- Rewrite the LHS succ 1 * m to 1 * m + m
  rw [succ_mul]
  -- Simplify LHS from 1 * m + m to m + m by identity property of multiplication
  rw [one_mul]

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem truncated_mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Induct on b, with b = 0 as the base case and the inductive hypothesis a * b = a * b + a * c. There are now two proof goals, prove base case: a * (0 + c) = a * 0 + a * c, and inductive step: a * (succ b + c) = a * succ b + a * c
  induction b with b hb
    -- First prove base case. Simplify LHS a * (0 + c) to a * c and RHS a * 0 + a * c to 0 + a * c and then simplify to a * c
  rw [zero_add, mul_zero, zero_add]

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem truncated_mul_add_2 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Induct on a, with a = 0 as the base case and the inductive hypothesis a * (b + c) = a * b + a * c. There are now two proof goals, prove base case: 0 * (b + c) = 0 * b + 0 * c, and inductive step: succ a * (b + c) = succ a * b + succ a * c
  induction a with a ha
    -- First prove base case. Simplify LHS to 0 and RHS to 0 + 0 and then 0 by applying the rules of multiplication and addition with zero
  rw [zero_mul, zero_mul, zero_mul, zero_add]

theorem truncated_mul_add_3 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a * (b + d) = a * b + a * d. There are now two proof goals, prove base case: a * (b + 0) = a * b + a * 0, and inductive step: a * (b + succ d) = a * b + a * succ d.
  induction c with d hd
  -- First prove the base case. Simplify both sides of the equation by replacing 'b + 0' with 'b', 'a * 0' with '0', and 'a * b + 0' with 'a * b'. Now the LHS and RHS are: a * b = a * b
  rw [add_zero, mul_zero, add_zero]

-- Proof Statement: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem truncated_add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- Rewrite LHS using the commutative property of multiplication and the distributive property of multiplication over addition. This changes (a + b) * c to c * a + c * b.
  rw [mul_comm, mul_add]
  -- Apply the commutative property of multiplication everywhere to LHS, changing c * a + c * b to a * c + b * c
  repeat rw [mul_comm c]

theorem truncated_mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a * b * d = a * (b * d). There are now two proof goals, prove base case: a * b * 0 = a * (b * 0), and inductive step: a * b * succ d = a * (b * succ d).
  induction c with d hd
  -- First prove base case. Rewrite LHS and RHS using the fact that any natural number multiplied by zero equals zero, simplifying the equation to 0 = 0
  rw [mul_zero, mul_zero, mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- Next prove inductive step. Rewrite LHS from a * b * succ d to a * b * d + a * b
  rw [mul_succ]
    -- Rewrite RHS from a * (b * succ d) to a * (b * d + b)
  rw [mul_succ]
    -- Rewrite LHS a * b * d + a * b using the inductive hypothesis to a * (b * d) + a * b
  rw [hd]
    -- Rewrite RHS using the distributive property of multiplication over addition, changing a * (b * d + b) to a * (b * d) + a * b
  rw [mul_add]


-- Truncated Theorems Report:

-- truncated_mul_one: 3 steps kept

-- truncated_zero_mul: 4 steps kept

-- truncated_succ_mul: 2 steps kept

-- truncated_mul_comm: 3 steps kept

-- truncated_mul_comm_2: 2 steps kept

-- truncated_one_mul: 2 steps kept

-- truncated_two_mul: 3 steps kept

-- truncated_mul_add: 2 steps kept

-- truncated_mul_add_2: 2 steps kept

-- truncated_mul_add_3: 2 steps kept

-- truncated_add_mul: 2 steps kept

-- truncated_mul_assoc: 5 steps kept
