import Game.Levels.Addition
import Game.MyNat.Multiplication
-- import Game.Levels.Multiplication.L08add_mul

namespace MyNat

-- Proof Statement: Prove the multiplicative identity property, the multiplication of m * 1 is m, for all natural numbers
theorem mul_one (m : ℕ) : m * 1 = m := by
  -- Rewrite 1 as succ 0, using the axiom that succ 0 = 1
  rw [one_eq_succ_zero]
  -- Rewrite LHS m * succ 0 to m * 0 + m using the definition of multiplication with a successor.
  rw [mul_succ]
  -- Simplify m * 0 + m to 0 + m on LHS
  rw [mul_zero]
  -- Rewrite the LHS 0 + m = m
  rw [zero_add]
  -- Prove LHS and RHS are equal, m = m, completing the proof
  rfl

-- Proof Statement: Prove the multiplicative identity property, the multiplication of m * 1 is m, for all natural numbers
theorem mul_one_train2 (m : ℕ) : m * 1 = m := by
  -- m * succ 0 = m
  rw [one_eq_succ_zero]
  -- m * succ 0 = m -> m * 0 + m = m
  rw [mul_succ]
  -- m * 0 + m = m -> 0 + m = m
  rw [mul_zero]
  -- 0 + m = m -> 0 + (0 + m) = 0 + m
  rw [← zero_add m]
  -- 0 + (0 + m) = 0 + m -> 0 + m + 0 = 0 + m
  rw [add_comm]
  -- 0 + m = 0 + m -> 0 + m + 0 = 0 + m
  rw [add_zero]
  -- lhs = rhs
  rfl

theorem mul_one_test (m : ℕ) : m * 1 = m := by
  -- We know that 1 is the successor of 0 so by definition of multiplication we have m * 1 = m * 0 + m
  rw [one_eq_succ_zero, mul_succ]
  -- By definition of multiplicationo and addition, we simplify m * 0 + m to m.
  rw [mul_zero, zero_add]
  -- The lhs and rhs are equal, completing the proof
  rfl

-- Proof Statement: Prove that 0 * m = m for all natural numbers
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
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
  -- Prove LHS and RHS are equal, 0 = 0, completing the proof
  rfl

-- Proof Statement: Prove that 0 * m = m for all natural numbers
theorem zero_mul_train2 (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- First prove base case. Simplify LHS 0 * 0 to 0
  rw [mul_zero]
  -- The base case is not complete.
  rfl
  -- Now for the inductive step. Rewrite LHS 0 * succ (d) to 0 * d + 0, using the definition of multiplication
  rw [mul_succ]
  -- Simplify the LHS 0 * d + 0 to 0 + 0 using the definition of addition
  rw [add_zero]
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd

-- Proof Statement: Prove that 0 * m = m for all natural numbers
theorem zero_mul_test (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- 0 * 0 = 0 -> 0 = 0
  rw [mul_zero]
  -- That proves the base case.
  rfl
  -- 0 * succ d = 0 -> 0 * d + 0 = 0 -> 0 * d = 0
  rw [mul_succ, add_zero]
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd
  -- First we prove base case. Simplify the LHS from succ a * 0 to 0
  rw [mul_zero]
  -- Simplify LHS a * 0 = 0
  rw [mul_zero]
-- Simplify RHS 0 + 0 to 0
  rw [add_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- Now prove inductive step. We rewrite LHS succ a * succ d to succ a * d + succ a
  rw [mul_succ]
  -- Expand the RHS from a * succ d + succ d to a * d + a + succ d
  rw [mul_succ]
  -- Rewrite the LHS  succ a * d + succ a to a * d + d + succ a using the inductive hypothesis
  rw [hd]
  -- Rewrite the LHS  a * d + d + succ a to succ (a * d + d + a)
  rw [add_succ]
  -- Rewrite RHS, changing a * d + a + succ d to succ (a * d + a + d)
  rw [add_succ]
  -- Apply  commutative property of additionin LHS: a * d + d + a to a * d + a + d
  rw [add_right_comm]
  -- Prove LHS and RHS are equal, succ (a * d + a + d) = succ (a * d + a + d), completing the proof
  rfl

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_train2 (a b : ℕ) : succ a * b = a * b + b := by
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
  -- Rewrite the LHS using the inductive hypothesis
  rw [hd]
  -- Apply the commutative property of addition in LHS: a * d + a + d to a * d + d + a
  rw [add_right_comm]
  -- The inductive step is complete.
  rfl

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_test (a b : ℕ) : succ a * b = a * b + b := by
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
  -- succ (a * d + d + a) = succ (d + a * d + a) -> succ (a * d + d + a) = succ (a * d + d + a)
  rw [add_comm d]
  -- This completes the inductive step.
  rfl

-- Proof Statement: Prove that multiplication is commutative, that is a * b  = b * a for all natural numbers
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a. There are now two proof goals, prove base case: a * 0 = 0 * a, and inductive step: a * succ d = succ d * a.
  induction b with d hd
  -- First we prove base case. Simplify RHS 0 * a to 0
  rw [zero_mul]
  -- Simplify LHS a * 0 to 0
  rw [mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- Next prove inductive step. Rewrite RHS succ d * a to d * a + a
  rw [succ_mul]
  -- Rewrite the RHS from d * a + a to a * d + a using the inductive hypothesis
  rw [← hd]
  -- Rewrite the LHS, changing a * succ d to a * d + a
  rw [mul_succ]
  -- Prove LHS and RHS are equal, a * d + a = a * d + a, completing the proof
  rfl

  -- Proof Statement: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_train2 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: a * 0 = 0 * a -> 0 = 0 * a by definition of multiplication
  rw [mul_zero, zero_mul]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case.
  rfl
  -- Next prove inductive step: a * succ d = succ d * a -> a * d + a = d * a + a by definition of multiplication
  rw [mul_succ, succ_mul]
  -- a * d + a = succ d * a -> a * d + a = d * a + a by the inductive hypothesis
  rw [hd]
  -- a * d + a = d * a + a -> d * a + a = d * a + a by the commutative property of addition
  rw [add_comm]
  -- LHS and RHS are equal, completing the proof.
  rfl

-- Proof Statement: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_test (a b : ℕ) : a * b = b * a := by
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
  -- a * d + a = d * a + a -> d * a + a = d * a + a
  rw [hd]
  -- Prove LHS and RHS are equal, a * d + a = a * d + a, completing the proof.
  rfl

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem one_mul (m : ℕ): 1 * m = m := by
  -- Apply the commutative property of multiplication to rewrite LHS from 1 * m to m * 1
  rw [mul_comm]
  -- Simplify m * 1 to m
  rw [mul_one]
  -- Prove LHS and RHS are equal, m = m, completing the proof
  rfl

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem one_mul_train2 (m : ℕ): 1 * m = m := by
  -- 1 * m = m -> m * 1 = m -> m = m by the commutative property of multiplication
  rw [mul_comm, mul_one]
  -- Prove LHS and RHS are equal, m = m, completing the proof
  rfl

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem one_mul_test (m : ℕ): 1 * m = m := by
  -- 1 * m = m -> m * 1 = m
  rw [mul_comm]
  -- m * 1 = m -> m = m
  rw [mul_one]
  -- Prove LHS and RHS are equal, m = m, completing the proof
  rfl

-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem two_mul (m : ℕ): 2 * m = m + m := by
  -- Rewrite 2 as succ(1), changing LHS from 2 * m to succ 1 * m
  rw [two_eq_succ_one]
  -- Rewrite the LHS succ 1 * m to 1 * m + m
  rw [succ_mul]
  -- Simplify LHS from 1 * m + m to m + m by identity property of multiplication
  rw [one_mul]
  -- Prove LHS and RHS are equal, m + m = m + m, completing the proof
  rfl


-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_train2 (m : ℕ): 2 * m = m + m := by
  -- Rewrite LHS from 2 * m to succ 1 * m and simplify to m * m using identity property of multiplication
  rw [two_eq_succ_one, succ_mul, one_mul]
  -- Prove LHS and RHS are equal, m + m = m + m, completing the proof
  rfl

-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_test (m : ℕ): 2 * m = m + m := by
  -- 2 * m = m + m -> succ 1 * m = m + m -> m + m = m + m
  rw [two_eq_succ_one, succ_mul, one_mul]
  -- LHS and RHS are equal, completing the proof
  rfl


-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Induct on b, with b = 0 as the base case and the inductive hypothesis a * b = a * b + a * c. There are now two proof goals, prove base case: a * (0 + c) = a * 0 + a * c, and inductive step: a * (succ b + c) = a * succ b + a * c
    induction b with d hd
    -- First prove base case. Simplify LHS a * (0 + c) to a * c and RHS a * 0 + a * c to 0 + a * c and then simplify to a * c
    rw [zero_add, mul_zero, zero_add]
    -- Prove LHS and RHS are equal, a * c = a * c, completing the base case
    rfl
    -- Next prove the inductive step. Rewrite LHS a * (succ b + c) to a * succ (b + c) and then to  a * (b + c) + a
    rw [succ_add, mul_succ]
    -- Rewrite RHS from a * succ b + a * c to a * b + a + a * c and then rearrange terms to a * b + a * c + a
    rw [mul_succ, add_right_comm]
    -- Rewrite the LHS a * (b + c) + a to a * b + a * c + a using the inductive hypothesis
    rw [hd]
    -- Prove LHS and RHS are equal, a * b + a * c + a = a * b + a * c + a, completing the proof
    rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_train1 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Proof by induction on b, with a * (0 + c) = a * 0 + a * c as the base case and  a * (succ b + c) = a * succ b + a * c as the inductive step.
    induction b with d hd
    -- First prove base case. a * (0 + c) = a * 0 + a * c -> a * c = a * 0 + a * c -> a * c = 0 + a * c -> a * c = a * c
    rw [zero_add, mul_zero, zero_add]
    -- The base case is complete.
    rfl
    -- Next prove inductive step. a * (succ b + c) = a * succ b + a * c -> a * succ (b + c) = a * succ b + a * c -> a * (b + c) + a = a * b + a * c + a
    rw [succ_add, mul_succ]
    -- a * (b + c) + a = a * b + a * c + a -> a * (b + c) + a = a * b + a + a * c -> a * (b + c) + a = a * b + a * c + a
    rw [mul_succ, add_right_comm]
    -- a * (b + c) + a = a * b + a * c + a -> a * b + a * c + a = a * b + a * c + a using the inductive hypothesis
    rw [hd]
    -- The inductive step is complete. So the whole proof is complete.
    rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_test1 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
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
    -- a * (b + c) + a = a * b + a * c + a -> a * b + a * c + a = a * b + a * c + a using the inductive hypothesis
    rw [hd]
    -- The inductive step is complete. So the whole proof is complete.
    rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_train2 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Induct on a, with a = 0 as the base case and the inductive hypothesis a * (b + c) = a * b + a * c. There are now two proof goals, prove base case: 0 * (b + c) = 0 * b + 0 * c, and inductive step: succ a * (b + c) = succ a * b + succ a * c
    induction a with d hd
    -- First prove base case. Simplify LHS to 0 and RHS to 0 + 0 and then 0 by applying the rules of multiplication and addition with zero
    rw [zero_mul, zero_mul, zero_mul, zero_add]
    -- Prove LHS and RHS are equal, 0 = 0, completing base case
    rfl
    -- Next prove inductive step. Expand LHS from succ a * (b + c) to a * (b + c) + (b + c) . Expand RHS from succ a * b + succ a * c to a * b + b + (a * c + c)
    rw [succ_mul, succ_mul, succ_mul]
    -- Rewrite LHS using the inductive hypothesis from a * (b + c) + (b + c) to a * b + a * c + (b + c)
    rw [hd]
    -- Apply the associative property of addition everywhere appropriate. Simplify the equation  to: a * b + a * c + (b + c) = a * b + b + (a * c + c)
    repeat rw [add_assoc]
    -- Rewrite LHS by applying the associative property of addition to the term a*c, then swapping the terms b and a*c, and finally applying the associative property of addition. This results in the final equation a * b + (b + (a * c + c)) = a * b + (b + (a * c + c))
    rw [← add_assoc (d*c), add_comm _ b, add_assoc]
    -- -- Prove LHS and RHS are equal, a * b + (b + (a * c + c)) = a * b + (b + (a * c + c)), completing inductive step
    rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_test2 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a * (b + d) = a * b + a * d. There are now two proof goals, prove base case: a * (b + 0) = a * b + a * 0, and inductive step: a * (b + succ d) = a * b + a * succ d.
  induction c with d hd
  -- First prove the base case. Simplify both sides of the equation by replacing 'b + 0' with 'b', 'a * 0' with '0', and 'a * b + 0' with 'a * b'. Now the LHS and RHS are: a * b = a * b
  rw [add_zero, mul_zero, add_zero]
  -- Prove LHS and RHS are equal, a * b = a * b, completing base case
  rfl
  -- Next prove inductive step. Rewrite the LHS from a * (b + succ d) to a * b + a * succ d and then simplify to a * (b + d) + a. Then, rewrite a * succ d to a * d + a using the definition of multiplication with succ. Then, apply the inductive hypothesis hd to rewrite a * succ d to a * d + a. Finally, rewrite a * succ d to a * d + a and use the associative property of addition to rearrange the terms to a * b + (a * d + a).
  rw [add_succ, mul_succ]
  -- Rewrite LHS a * b + (a * d + a), to a * b + a * d + a using the inductive hypothesis
  rw [hd]
  -- Rewrite RHS a * b + a * succ d toa * b + (a * d + a) and rearrange the LHS a * b + a * d + a to a * b + (a * d + a)
  rw [mul_succ, add_assoc]
  -- Prove LHS and RHS are equal, a * b + (a * d + a) = a * b + (a * d + a), completing base case
  rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- Rewrite LHS using the commutative property of multiplication and the distributive property of multiplication over addition. This changes (a + b) * c to c * a + c * b.
  rw [mul_comm, mul_add]
  -- Apply the commutative property of multiplication everywhere to LHS, changing c * a + c * b to a * c + b * c
  repeat rw [mul_comm c]
  -- Prove LHS and RHS are equal, a * c + b * c = a * c + b * c, completing base case
  rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul_train2 (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- (a + b) * c = a * c + b * c -> c * (a + b) = a * c + b * c
  rw [mul_comm]
  -- c * (a + b) = a * c + b * c -> c * a + c * b = a * c + b * c
  rw [mul_add]
  -- c * a + c * b = a * c + b * c -> a * c + c * b = a * c + b * c
  rw [mul_comm]
  -- a * c + c * b = a * c + b * c -> a * c + b * c = a * c + b * c
  rw [mul_comm b]
  -- Prove LHS and RHS are equal, completing the proof
  rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul_test (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- Rewrite LHS using the commutative property of multiplication and the distributive property of multiplication over addition.
  rw [mul_comm, mul_add]
  -- Apply the commutative property of multiplication everywhere to LHS
  repeat rw [mul_comm c]
  -- Prove LHS and RHS are equal, completing the proof
  rfl

-- Proof Statement: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
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
  -- Prove LHS and RHS are equal, a * (b * d) + a * b = a * (b * d) + a * b, completing base case
  rfl

-- Proof Statement: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc_train2 (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with (a * b) * 0 = a * (b * 0) as the base case and (a * b) * succ d = a * (b * succ d) as the inductive step.
  induction c with d hd
  -- a * b * 0 = a * (b * 0) -> 0 = a * 0 -> 0 = 0
  rw [mul_zero, mul_zero, mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- for the inductive case, a * b * succ d = a * (b * succ d) -> a * b * d + a * b = a * (b * succ d)
  rw [mul_succ]
  -- a * b * d + a * b = a * (b * succ d) -> a * b * d + a * b = a * (b * d + b)
  rw [mul_succ]
  -- a * b * d + a * b = a * (b * d + b) -> a * b * d + a * b = a * (b * d) + a * b
  rw [mul_add]
  -- a * b * d + a * b = a * (b * d) + a * b -> a * b * d + a * b = a * b * d + a * b
  rw [← hd]
  -- Prove LHS and RHS are equal, completing base case
  rfl

-- Proof Statement: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc_test (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with (a * b) * 0 = a * (b * 0) as the base case and (a * b) * succ d = a * (b * succ d) as the inductive step.
  induction c with d hd
  -- First prove base case. Rewrite LHS and RHS using the definition of multiplication with zero, simplifying the equation to 0 = 0
  rw [mul_zero, mul_zero, mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- For the inductive step, a * b * succ d = a * (b * succ d) simplifies to a * b * d + a * b = a * (b * d + b) using the definition of multiplication with succ
  rw [mul_succ, mul_succ]
  -- Use the inductive hypothesis to simplify this further to a * (b * d) + a * b = a * (b * d + b)
  rw [hd]
  -- simplify to a * (b * d) + a * b = a * (b * d) + a * b using the distributive property of multiplication over addition
  rw [mul_add]
  -- The LHS and RHS are equal, completing the proof
  rfl
