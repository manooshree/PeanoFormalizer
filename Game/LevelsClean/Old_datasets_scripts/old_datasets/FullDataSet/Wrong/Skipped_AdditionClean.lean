import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial
-- import Game_Levels_Tut

namespace MyNat


--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem skipped_zero_add (n : ℕ) : 0 + n = n := by
-- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd
-- First prove base case. Reduce LHS 0 + 0 = 0.
  rw [add_zero]
-- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
  rfl
-- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d)
  rw [add_succ]
-- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
  rfl -- error

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem skipped_succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
  rfl -- error


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem skipped_succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
  rfl -- error

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem skipped_succ_add_logically_eq (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
  induction b with n hn
-- We start by proving the base case using the fact that c + 0 = c ∀ c ∈ ℕ and setting c := a giving us succ(a) + 0 = succ(a)
  rw [add_zero]
-- Rewrite the left hand side using the hypothesis giving us succ(succ(a+n)) = succ(succ(a+n))
  rw [hn] -- error
-- Hence we are done.
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem skipped_succ_add_logical_deviation_1 (a b : ℕ) : succ a + b = succ (a + b) := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
induction b with n hn
-- We again use the fact that a + succ(b) = succ(a + b) ∀ a, b ∈ ℕ on the right hand side and set a := a and b := n giving us succ(succ(a) + n) = succ(succ(a+n))
rw [add_succ] -- error
-- Rewrite the right hand side using the hypothesis giving us succ(succ(a + n)) = succ(succ(a) + n)
rw [← hn]
-- Hence we are done.
rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem skipped_succ_add_logical_deviation_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
 induction b with n hn
-- We start by proving the base case using the fact that succ(a+b) = a + succ(b) and setting b = 0 and substituting on the RHS
 rw [← add_succ]
-- We use the fact that c + 0 = c ∀ c ∈ ℕ and set c := succ(a) to get succ(a) = a + succ(0)
 rw [add_zero]
-- Rewrite the right hand side using the hypothesis giving us succ(succ(a) + n) = succ(succ(a) + n)
 rw [← hn] -- error
-- Hence we are done.
 rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem skipped_add_comm (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a.
  rw [add_zero]
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d)
  rw [add_succ] -- error
-- Rewrite RHS succ (d) + a = succ (d + a)
  rw [succ_add]
-- Rewrite LHS succ (a + d) to succ (d + a) using the inductive hypothesis
  rw [hd]
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
  rfl



-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem skipped_add_comm_2 (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d) and RHS succ (d) + a = succ (d + a). Then, use the inductive hypothesis to rewrite succ (a + d) = succ (d + a)
  rw [add_succ, succ_add, hd] -- error
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem skipped_add_comm_3 (a b : ℕ) : a + b = b + a := by
-- Induct on a, with d = 0 as the base case and the inductive hypothesis d + b = b + d. There are now two proof goals, prove base case: 0 + b = b + 0 and the inductive step: succ d + b = b + succ d
  induction a with d hd
-- First prove base case. Simplify RHS b + 0 = b and LHS 0 + b = b
  rw [add_zero, zero_add] -- error
-- Now prove the inductive step. Rewrite RHS b + succ d = succ (b + d) and LHS succ (d) + b = succ (d + b). Then, use the inductive hypothesis to rewrite succ (d + b) = succ (b + d)
  rw [add_succ, succ_add, hd]
-- Prove LHS and RHS are equal, succ (b + d) = succ (b + d), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem skipped_add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d))
  induction c with d hd
  -- Rewrite RHS a + (b + succ d) to a + succ (b + d)
  rw [add_succ] -- error
  -- Use the inductive hypothesis to rewrite the left-hand side, changing succ (a + b + d) to succ (a + (b + d))
  rw [hd]
--  Rewrite the RHS, a + succ (b + d) to succ (a + (b + d))
  rw [add_succ]
-- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem skipped_add_assoc_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d)).
  induction c with d hd
  -- Now prove the inductive step. Rewrite the LHS: a + b + succ (d) to succ (a + b + d) and then to succ (a + (b + d)), using the inductive hypothesis. Change the RHS: a + (b + succ d) to a + succ (b + d) to succ (a + (b + d))
  rw [add_succ, add_succ, hd, add_succ] -- error
  -- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem skipped_add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS of the equation, changing a + b + c to a + (b + c)
  rw [add_assoc] -- error
  -- Rewrite the LHS of the equation by applying the commutative property of addition to b and c, LHS is now a + (c + b)
  rw [add_comm b]
  -- Prove LHS and RHS are equal, a + (c + b) = a + (c + b), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem skipped_add_right_comm_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc] -- error
  -- Rewrite the LHS using the commutative property of addition for b and c: a + (b + c) to a + (c + b).
  rw [add_comm b c]
  -- Prove LHS and RHS are equal, completing the proof.
  rfl



-- Skipped Steps Theorems Report:

-- skipped_zero_add: 1 steps skipped

-- skipped_succ_add: 5 steps skipped

-- skipped_succ_add_2: 3 steps skipped

-- skipped_add_comm: 2 steps skipped

-- skipped_add_comm_2: 2 steps skipped

-- skipped_add_comm_3: 1 steps skipped

-- skipped_add_assoc: 4 steps skipped

-- skipped_add_assoc_2: 2 steps skipped

-- skipped_add_right_comm: 1 steps skipped

-- skipped_add_right_comm_2: 1 steps skipped

-- skipped_succ_add_logically_eq: 4 steps skipped

-- skipped_succ_add_logical_deviation_1: 4 steps skipped

-- skipped_succ_add_logical_deviation_2: 5 steps skipped
