import Game.LevelsClean.AdditionClean
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
theorem mul_one_dev_1 (m : ℕ) : m * 1 = m := by
  -- m * succ 0 = m
  rw [one_eq_succ_zero]
  -- m * 0 + m = m
  rw [mul_succ]
  -- 0 + m = m
  rw [mul_zero]
  -- 0 + (0 + m) = 0 + m
  rw [← zero_add m]
  -- 0 + m + 0 = 0 + m
  rw [add_comm]
  -- 0 + m = 0 + m
  rw [add_zero]
  -- lhs = rhs
  rfl

theorem mul_one_dev_2 (m : ℕ) : m * 1 = m := by
  -- We know that 1 is the successor of 0 so by definition of multiplication we have m * 1 = m * 0 + m
  rw [one_eq_succ_zero, mul_succ]
  -- By the fact that 1 = succ 0 and that 0 + n = n, we obtain m
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
theorem zero_mul_dev_1 (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- First prove base case. Simplify LHS 0 * 0 to 0
  rw [mul_zero]
  -- The base case is now complete.
  rfl
  -- Now for the inductive step. Rewrite LHS 0 * succ (d) to 0 * d + 0, using the definition of multiplication
  rw [mul_succ]
  -- Simplify the LHS 0 * d + 0 to 0 * d using the definition of addition
  rw [add_zero]
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd

-- Proof Statement: Prove that 0 * m = m for all natural numbers
theorem zero_mul_dev_2 (m : ℕ) : 0 * m = 0 := by
  -- Proof by induction on m with base case 0 * 0 = 0 and inductive step 0 * d + 1 = 0
  induction m with d hd
  -- the base case becomes 0 = 0
  rw [mul_zero]
  -- That proves the base case.
  rfl
  -- the inductive case becomes 0 * d = 0
  rw [mul_succ, add_zero]
  -- This is exactly the inductive hypothesis so we can complete the proof.
  exact hd


-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd
  -- First we prove base case. Simplify the LHS from succ a * 0 to 0 using the fact that a * 0 = 0
  rw [mul_zero]
  -- Simplify LHS a * 0 = 0 hence we obtain 0 = 0 + 0
  rw [mul_zero]
-- Simplify RHS 0 + 0 to 0 hence we obtain 0 = 0
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
  -- Apply the fact that a + b + c = a + c + b on LHS obtaining a * d + d + a to a * d + a + d
  rw [add_right_comm]
  -- Prove LHS and RHS are equal, succ (a * d + a + d) = succ (a * d + a + d), completing the proof
  rfl


-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_dev_1 (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd
  -- First we prove base case. Simplify succ a * 0 = a * 0 + 0 to 0 = 0 by definition of multiplication and addition
  rw [add_zero, mul_zero, mul_zero]
  -- The base case is complete.
  rfl
  -- Now prove inductive step. We rewrite the equation to succ a * d + succ a = a * d + a + succ d
  rw [mul_succ, mul_succ]
  -- Expand the equation to succ (succ a * d + a) = succ (a * d + a + d) using properties of the successor
  rw [add_succ, add_succ]
  -- Rewrite the LHS using the inductive hypothesis obtaining succ (a * d + d + a)
  rw [hd]
  -- Apply the commutative property of addition in LHS: a * d + a + d to a * d + d + a
  rw [add_right_comm]
  -- LHS = RHS hence, The inductive step is complete.
  rfl

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_dev_2 (a b : ℕ) : succ a * b = a * b + b := by
  -- Proof by induction on b, with succ a * 0 = a * 0 + 0 as the base case and the inductive case as succ a * d + 1 = a * d + 1 + d + 1.
  induction b with d hd
  -- 0 = a * 0 + 0
  rw [mul_zero]
  -- 0 = 0 + 0
  rw [mul_zero]
  -- 0 = 0
  rw [add_zero]
  -- Base case is complete.
  rfl
  -- succ a * succ d = succ d + a * succ d
  rw [add_comm]
  -- succ a * d + succ a = succ d + a * succ d
  rw [mul_succ]
  -- succ (succ a * d + a) = succ d + a * succ d
  rw [add_succ]
  -- succ (succ a * d + a) = succ d + (a * d + a)
  rw [mul_succ]
  -- succ (succ a * d + a) = succ (d + (a * d + a))
  rw [succ_add]
  -- succ (a * d + d + a) = succ (d + (a * d + a))
  rw [hd]
  -- succ (a * d + d + a) = succ (d + a * d + a)
  rw [← add_assoc]
  -- succ (a * d + d + a) = succ (a * d + d + a)
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
theorem mul_comm_dev_1 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: we obtain 0 = 0 * a
  rw [mul_zero]
  -- 0 = 0
  rw [zero_mul]
  -- 0 = 0, completing base case.
  rfl
  -- Next prove inductive step: we obtain a * d + a = succ d * a.
  rw [mul_succ]
  -- a * d + a = d * a + a
  rw [succ_mul]
  -- d * a + a = d * a + a
  rw [hd]
  -- d * a + a = d * a + a, completing the proof.
  rfl


  -- Proof Statement: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_dev_2 (a b : ℕ) : a * b = b * a := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
  induction b with d hd
  -- First prove base case: 0 = 0 by definition of multiplication
  rw [mul_zero, zero_mul]
  -- 0 = 0, completing base case.
  rfl
  -- Next prove inductive step: we obtain a * d + a = d * a + a by definition of multiplication
  rw [mul_succ, succ_mul]
  -- d * a + a = d * a + a by the inductive hypothesis
  rw [hd]
  -- a + d * a = a + d * a by the commutative property of addition
  rw [add_comm]
  -- LHS and RHS are equal, completing the proof.
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
theorem one_mul_dev_1 (m : ℕ): 1 * m = m := by
  -- m * 1 = m
  rw [mul_comm]
  --  m = m
  rw [mul_one]
  -- m = m, completing the proof
  rfl

-- Proof Statement: Prove that 1 * m = m, for all natural numbers
theorem one_mul_dev_2 (m : ℕ): 1 * m = m := by
  -- we obtain m = m by the commutative property of multiplication
  rw [mul_comm, mul_one]
  -- m = m, completing the proof
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
theorem two_mul_dev_1 (m : ℕ): 2 * m = m + m := by
  -- Rewrite LHS from 2 * m to succ 1 * m and simplify to m + m using identity property of multiplication
  rw [two_eq_succ_one, succ_mul, one_mul]
  -- Prove LHS and RHS are equal, m + m = m + m, completing the proof
  rfl

-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_dev_2 (m : ℕ): 2 * m = m + m := by
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
theorem mul_add_dev_1 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Proof by induction on b
    induction b with d hd
    -- Begin the base case: a * c = a * 0 + a * c
    rw [zero_add]
    -- a * c = 0 + a * c
    rw [mul_zero]
    -- a * c = a * c
    rw [zero_add]
    -- The base case is complete.
    rfl
    -- Next prove inductive step. a * (b + c) + a = a * succ b + a * c
    rw [succ_add, mul_succ]
    -- a * (b + c) + a = a * b + a * c + a
    rw [mul_succ, add_right_comm]
    --  a * b + a * c + a = a * b + a * c + a using the inductive hypothesis
    rw [hd]
    -- The inductive step is complete. So the whole proof is complete.
    rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers a * (b + c) = a * b + a * c
theorem mul_add_dev_2 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
    -- Proof by induction on b, with a * (0 + c) = a * 0 + a * c as the base case and  a * (succ b + c) = a * succ b + a * c as the inductive step.
    induction b with d hd
    -- First prove base case. a * (0 + c) = a * 0 + a * c becomes a * c = a * c by definition of multiplication and addition
    rw [zero_add, mul_zero, zero_add]
    -- The base case is complete.
    rfl
    -- Next prove inductive step. a * (succ b + c) = a * succ b + a * c becomes a * (b + c) + a = a * succ b + a * c + a by definition of multiplication and addition
    rw [succ_add, mul_succ]
    -- a * (b + c) + a = a * b + a * c + a becomes a * (b + c) + a = a * b + a * c + a by the definition of multiplication and the commutative property of addition
    rw [mul_succ, add_right_comm]
    -- a * (b + c) + a = a * b + a * c + a becomes a * b + a * c + a = a * b + a * c + a using the inductive hypothesis
    rw [hd]
    -- The inductive step is complete. So the whole proof is complete.
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
theorem add_mul_dev_1 (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  -- c * (a + b) = a * c + b * c
  rw [mul_comm]
  -- c * a + c * b = a * c + b * c
  rw [mul_add]
  -- a * c + c * b = a * c + b * c
  rw [mul_comm]
  -- a * c + c * b = a * c + c * b
  rw [mul_comm b]
  -- Prove LHS and RHS are equal, completing the proof
  rfl

-- Proof Statement: Prove that multiplication is distributive over addition. In other words, for all natural numbers (a + b) * c = a * c + b * c
theorem add_mul_dev_2 (a b c : ℕ) : (a + b) * c = a * c + b * c := by
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
  repeat rw [mul_zero]
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
theorem mul_assoc_dev_1 (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c
  induction c with d hd
  -- The base case becomes 0 = 0 using properties of multiplication by zero
  repeat rw [mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- for the inductive case, we obtain a * b * d + a * b = a * (b * succ d)
  rw [mul_succ]
  -- a * b * d + a * b = a * (b * d + b)
  rw [mul_succ]
  -- a * b * d + a * b = a * (b * d) + a * b
  rw [mul_add]
  -- a * b * d + a * b = a * b * d + a * b
  rw [← hd]
  -- Prove LHS and RHS are equal, completing base case
  rfl

-- Proof Statement: Prove that multiplication is associative for all natural numbers, that is (a * b) * c = a * (b * c)
theorem mul_assoc_dev_2 (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  -- Induct on c, with (a * b) * 0 = a * (b * 0) as the base case and (a * b) * succ d = a * (b * succ d) as the inductive step.
  induction c with d hd
  -- First prove base case. Rewrite LHS and RHS using the definition of multiplication with zero, simplifying the equation to 0 = 0
  repeat rw [mul_zero]
  -- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
  -- For the inductive step, a * b * succ d = a * (b * succ d) simplifies to a * b * d + a * b = a * (b * d + b) using the definition of multiplication with succ
  repeat rw [mul_succ]
  -- Use the inductive hypothesis to simplify this further to a * (b * d) + a * b = a * (b * d + b)
  rw [hd]
  -- simplify to a * (b * d) + a * b = a * (b * d) + a * b using the distributive property of multiplication over addition
  rw [mul_add]
  -- The LHS and RHS are equal, completing the proof
  rfl
