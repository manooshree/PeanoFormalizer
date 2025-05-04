import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial
import Game.Levels.Addition

namespace MyNat


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem truncated_zero_add (n : ℕ) : 0 + n = n := by
-- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd
-- First prove base case. Reduce LHS 0 + 0 = 0.
  rw [add_zero]
-- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem truncated_succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
  rw [add_zero]
-- Prove succ (a) = succ (a), finishing the base case
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem truncated_succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
  rw [add_zero]

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem truncated_add_comm (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a.
  rw [add_zero]
-- Simplify RHS 0 + a = a
  rw [zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem truncated_add_comm_2 (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a and RHS 0 + a = a.
  rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem truncated_add_comm_3 (a b : ℕ) : a + b = b + a := by
-- Induct on a, with d = 0 as the base case and the inductive hypothesis d + b = b + d. There are now two proof goals, prove base case: 0 + b = b + 0 and the inductive step: succ d + b = b + succ d
  induction a with d hd
-- First prove base case. Simplify RHS b + 0 = b and LHS 0 + b = b
  rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, b = b, completing the base case.
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem truncated_add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d))
  induction c with d hd
  -- First prove base case. Simplify LHS a + b + 0 = a + b
  rw [add_zero]
    -- Reduce RHS a + (b + 0) to a + b
  rw [add_zero]

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem truncated_add_assoc_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d)).
  induction c with d hd
  -- First we prove the base case. Simplify the LHS and RHS both to a + b
  rw [add_zero, add_zero]
  -- Prove LHS and RHS are equal, a + b = a + b, completing the base case.
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem truncated_add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS of the equation, changing a + b + c to a + (b + c)
  rw [add_assoc]
  -- Rewrite the LHS of the equation by applying the commutative property of addition to b and c, LHS is now a + (c + b)
  rw [add_comm b]

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem truncated_add_right_comm_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Rewrite the LHS using the commutative property of addition for b and c: a + (b + c) to a + (c + b).
  rw [add_comm b c]

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem truncated_succ_add_logically_eq (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
  induction b with n hn
-- We start by proving the base case using the fact that c + 0 = c ∀ c ∈ ℕ and setting c := a giving us succ(a) + 0 = succ(a)
  rw [add_zero]
-- Now we can set c = succ(a) and use c + 0 = c ∀ c ∈ ℕ again to get succ(a) = succ(a)
  rw [add_zero]

-- THIS IS TOTALLY WEIRD BUT A DEVIATION NEVERTHELESS
-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem truncated_succ_add_logical_deviation_1 (a b : ℕ) : succ a + b = succ (a + b) := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
  induction b with n hn
-- We start by proving the base case using the fact that c + 0 = c ∀ c ∈ ℕ and setting c := succ(a) giving us succ(a) = succ(a + 0)
  rw [add_zero]
-- Now we can set c = a and use c + 0 = c ∀ c ∈ ℕ again to get succ(a) = succ(a)
  rw [add_zero]

theorem truncated_succ_add_logical_deviation_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
 induction b with n hn
-- We start by proving the base case using the fact that succ(a+b) = a + succ(b) and setting b = 0 and substituting on the RHS
 rw [← add_succ]


-- Truncated Theorems Report:

-- truncated_zero_add: 2 steps kept

-- truncated_succ_add: 3 steps kept

-- truncated_succ_add_2: 2 steps kept

-- truncated_add_comm: 3 steps kept

-- truncated_add_comm_2: 2 steps kept

-- truncated_add_comm_3: 2 steps kept

-- truncated_add_assoc: 2 steps kept

-- truncated_add_assoc_2: 2 steps kept

-- truncated_add_right_comm: 2 steps kept

-- truncated_add_right_comm_2: 2 steps kept

-- truncated_succ_add_logically_eq: 3 steps kept

-- truncated_succ_add_logical_deviation_1: 3 steps kept

-- truncated_succ_add_logical_deviation_2: 2 steps kept
