import Game.LevelsClean.AdditionClean
import Game.MyNat.Multiplication

namespace MyNat

-- Theorem Declaration: Prove the multiplicative identity property, the multiplication of m * 1 is m, for all natural numbers
theorem mul_one_dev_1 (m : ℕ) : m * 1 = m := by
  -- m * succ 0 = m
  rw [one_eq_succ_zero]
  -- m * succ 0 = m -> m * 0 + m = m
  rw [mul_succ]
  -- m * 0 + m = m -> 0 + m = m
  rw [mul_zero]
  -- 0 + (0 + m) = 0 + m -> 0 + m + 0 = 0 + m
  rw [add_comm]
  -- 0 + m = 0 + m -> 0 + m + 0 = 0 + m
  rw [add_zero]
  -- lhs = rhs
  rfl

-- Theorem Declaration:
theorem mul_one_dev_2 (m : ℕ) : m * 1 = m := by
  -- We know that 1 is the successor of 0 so by definition of multiplication we have m * 1 = m * 0 + m
  rw [one_eq_succ_zero, mul_succ]
  -- The lhs and rhs are equal, completing the proof
  rfl

-- Theorem Declaration: Prove that 0 * m = m for all natural numbers
theorem zero_mul_dev_1 (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- First prove base case. Simplify LHS 0 * 0 to 0
  rw [mul_zero]
  -- The base case is not complete.
  rfl
  -- Simplify the LHS 0 * d + 0 to 0 + 0 using the definition of addition
  rw [add_zero]
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd

-- Theorem Declaration: Prove that 0 * m = m for all natural numbers
theorem zero_mul_dev_2 (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- 0 * 0 = 0 -> 0 = 0
  rw [mul_zero]
  -- That proves the base case.
  rfl
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd

-- Theorem Declaration: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_dev_1 (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd
  -- First we prove base case. Simplify succ a * 0 = a * 0 + 0 to 0 = 0 by definition of multiplication and addition
  rw [add_zero, mul_zero, mul_zero]
  -- The base case is complete.
  rfl
  -- Now prove inductive step. We rewrite LHS succ a * succ d to succ a * d + succ a
  rw [mul_succ, mul_succ]
  -- Expand the RHS from a * succ d + succ d to a * d + a + succ d
  rw [add_succ, add_succ]
  -- Apply the commutative property of addition in LHS: a * d + a + d to a * d + d + a
  rw [add_right_comm]
  -- The inductive step is complete.
  rfl

-- Theorem Declaration: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_dev_2 (a b : ℕ) : succ a * b = a * b + b := by
  -- Proof by induction on b, with succ a * 0 = a * 0 + 0 as the base case and the inductive case as succ a * d + 1 = a * d + 1 + d + 1.
  induction b with d hd
  -- succ a * 0 = a * 0 + 0 -> 0 = a * 0 + 0
  rw [mul_zero]
  -- 0 = a * 0 + 0 -> 0 = 0 + 0
  rw [mul_zero]
  -- 0 = 0 + 0 -> 0 = 0
  rw [add_zero]
  -- Base case is complete.
  rfl
  -- succ a * succ d = a * succ d + succ d -> succ a * succ d = succ d + a * succ d
  rw [add_comm]
  -- succ a * succ d = succ d + a * succ d -> succ a * d + succ a = succ d + a * succ d
  rw [mul_succ]
  -- ucc a * d + succ a = succ d + a * succ d -> succ (succ a * d + a) = succ d + a * succ d
  rw [add_succ]
  -- succ (succ a * d + a) = succ d + a * succ d -> succ (succ a * d + a) = succ d + (a * d + a)
  rw [mul_succ]
  -- succ (succ a * d + a) = succ d + (a * d + a)-> succ (succ a * d + a) = succ (d + (a * d + a))
  rw [succ_add]
  -- succ (succ a * d + a) = succ (d + (a * d + a)) -> succ (a * d + d + a) = succ (d + (a * d + a))
  rw [hd]
  -- succ (a * d + d + a) = succ (d + (a * d + a)) -> succ (a * d + d + a) = succ (d + a * d + a)
  rw [← add_assoc]
  -- This completes the inductive step.
  rfl

-- Theorem Declaration: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_dev_1 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: a * 0 = 0 * a -> 0 = 0 * a by definition of multiplication
  rw [mul_zero, zero_mul]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case.
  rfl
  -- Next prove inductive step: a * succ d = succ d * a -> a * d + a = d * a + a by definition of multiplication
  rw [mul_succ, succ_mul]
  -- a * d + a = d * a + a -> d * a + a = d * a + a by the commutative property of addition
  rw [add_comm]
  -- LHS and RHS are equal, completing the proof.
  rfl

-- Theorem Declaration: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_dev_2 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: a * 0 = 0 * a -> 0 = 0 * a
  rw [mul_zero]
  -- Simplify RHS 0 = 0 * a -> 0 = 0
  rw [zero_mul]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case.
  rfl
  -- Next prove inductive step: a * succ d = succ d * a -> a * d + a = succ d * a.
  rw [mul_succ]
  -- a * d + a = succ d * a -> a * d + a = d * a + a
  rw [succ_mul]
  -- Prove LHS and RHS are equal, a * d + a = a * d + a, completing the proof.
  rfl

-- Theorem Declaration: Prove that 1 * m = m, for all natural numbers
theorem one_mul_dev_1 (m : ℕ): 1 * m = m := by
  -- 1 * m = m -> m * 1 = m -> m = m by the commutative property of multiplication
  rw [mul_comm, mul_one]

-- Theorem Declaration: Prove that 1 * m = m, for all natural numbers
theorem one_mul_dev_2 (m : ℕ): 1 * m = m := by
  -- 1 * m = m -> m * 1 = m
  rw [mul_comm]
  -- Prove LHS and RHS are equal, m = m, completing the proof
  rfl

-- Theorem Declaration: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_dev_1 (m : ℕ): 2 * m = m + m := by
  -- Rewrite LHS from 2 * m to succ 1 * m and simplify to m * m using identity property of multiplication
  rw [two_eq_succ_one, succ_mul, one_mul]

-- Theorem Declaration: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_dev_2 (m : ℕ): 2 * m = m + m := by
  -- 2 * m = m + m -> succ 1 * m = m + m -> m + m = m + m
  rw [two_eq_succ_one, succ_mul, one_mul]

-- Theorem Declaration: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_dev_1 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  -- Proof by induction on b, with a * (0 + c) = a * 0 + a * c as the base case and  a * (succ b + c) = a * succ b + a * c as the inductive step.
  induction b with d hd
  -- First prove base case. a * (0 + c) = a * 0 + a * c -> a * c = a * 0 + a * c -> a * c = 0 + a * c -> a * c = a * c
  rw [zero_add, mul_zero, zero_add]
  -- The base case is complete.
  rfl
  -- a * (b + c) + a = a * b + a * c + a -> a * (b + c) + a = a * b + a + a * c -> a * (b + c) + a = a * b + a * c + a
  rw [mul_succ, add_right_comm]
  -- a * (b + c) + a = a * b + a * c + a -> a * b + a * c + a = a * b + a * c + a using the inductive hypothesis
  rw [hd]
  -- The inductive step is complete. So the whole proof is complete.
  rfl

-- Theorem Declaration: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_dev_2 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  -- Proof by induction on b, with a * (0 + c) = a * 0 + a * c as the base case and  a * (succ b + c) = a * succ b + a * c as the inductive step.
  induction b with d hd
  -- First prove base case. a * (0 + c) = a * 0 + a * c -> a * c = a * c by definition of multiplication and addition
  rw [zero_add, mul_zero, zero_add]
  -- The base case is complete.
  rfl
  -- Next prove inductive step. a * (succ b + c) = a * succ b + a * c -> a * (b + c) + a = a * b + a * c + a by definition of multiplication and addition
  rw [succ_add, mul_succ]
  -- a * (b + c) + a = a * b + a * c + a -> a * (b + c) + a = a * b + a * c + a by the definition of multiplication and the commutative property of addition
  rw [mul_succ, add_right_comm]
  -- The inductive step is complete. So the whole proof is complete.
  rfl

-- Theorem Declaration: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul_dev_1 (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- (a + b) * c = a * c + b * c -> c * (a + b) = a * c + b * c
  rw [mul_comm]
  -- c * (a + b) = a * c + b * c -> c * a + c * b = a * c + b * c
  rw [mul_add]
  -- a * c + c * b = a * c + b * c -> a * c + b * c = a * c + b * c
  rw [mul_comm b]
  -- Prove LHS and RHS are equal, completing the proof
  rfl

-- Theorem Declaration: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul_dev_2 (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- Rewrite LHS using the commutative property of multiplication and the distributive property of multiplication over addition.
  rw [mul_comm, mul_add]
  -- Prove LHS and RHS are equal, completing the proof
  rfl

-- Theorem Declaration: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc_dev_1 (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with (a * b) * 0 = a * (b * 0) as the base case and (a * b) * succ d = a * (b * succ d) as the inductive step.
  induction c with d hd
  -- a * b * 0 = a * (b * 0) -> 0 = a * 0 -> 0 = 0
  rw [mul_zero, mul_zero, mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- for the inductive case, a * b * succ d = a * (b * succ d) -> a * b * d + a * b = a * (b * succ d)
  rw [mul_succ]
  -- a * b * d + a * b = a * (b * d + b) -> a * b * d + a * b = a * (b * d) + a * b
  rw [mul_add]
  -- a * b * d + a * b = a * (b * d) + a * b -> a * b * d + a * b = a * b * d + a * b
  rw [← hd]
  -- Prove LHS and RHS are equal, completing base case
  rfl

-- Theorem Declaration: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc_dev_2 (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with (a * b) * 0 = a * (b * 0) as the base case and (a * b) * succ d = a * (b * succ d) as the inductive step.
  induction c with d hd
  -- First prove base case. Rewrite LHS and RHS using the definition of multiplication with zero, simplifying the equation to 0 = 0
  rw [mul_zero, mul_zero, mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- Use the inductive hypothesis to simplify this further to a * (b * d) + a * b = a * (b * d + b)
  rw [hd]
  -- simplify to a * (b * d) + a * b = a * (b * d) + a * b using the distributive property of multiplication over addition
  rw [mul_add]
  -- The LHS and RHS are equal, completing the proof
  rfl

end MyNat
