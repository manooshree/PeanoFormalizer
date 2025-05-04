import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean

namespace MyNat

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  · rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
    rw [add_zero]
-- Prove succ (a) = succ (a), finishing the base case
    rfl
-- Now prove the inductive step. Rewrite succ (a) + succ (d) = succ (succ a + d)
  · rw [add_succ]
-- Rewrite succ (a + succ d) = succ (succ (a + d))
    rw [add_succ]
-- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
    rw [hd]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  · rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
    rw [add_zero]
-- Prove succ (a) = succ (a), finishing the base case
    rfl
-- Now prove the inductive step. Rewrite the LHS succ (a) + succ (d) = succ (succ (a + d)) and the RHS succ (a + succ d) = succ (succ (a + d)). Then rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
  · rw [add_succ, add_succ, hd]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_3 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
  -- First prove base case. Reduce LHS succ (a) + 0 = succ (a) and reduce RHS succ(a + 0) = succ (a)
  · rw [add_zero, add_zero]
  -- Prove succ (a) = succ (a), finishing the base case
    rfl
  · rw [add_succ, add_succ, hd]
  -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_4 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
  -- First prove base case. Reduce LHS succ (a) + 0 = succ (a) and reduce RHS succ(a + 0) = succ (a)
  · rw [add_zero, add_zero]
  -- Prove succ (a) = succ (a), finishing the base case
    rfl
  -- Now prove the inductive step. Rewrite succ (a) + succ (d) = succ (succ a + d)
  · rw [add_succ]
  -- Rewrite succ (a + succ d) = succ (succ (a + d))
    rw [add_succ]
  -- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
    rw [hd]
    -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_5 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
  -- First prove base case. Apply the simplification that a + 0 = a to everywhere appropriate. The simplified equation is succ a = succ a
  · repeat rw [add_zero]
  -- Prove succ (a) = succ (a), finishing the base case
    rfl
  -- Now prove the inductive step. Rewrite LHS succ (a) + succ (d) = succ (succ a + d)
  · rw [add_succ]
  -- Rewrite succ (a + succ d) = succ (succ (a + d))
    rw [add_succ]
  -- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
    rw [hd]
    -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_6 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
    -- First prove base case. Apply the simplification that a + 0 = a to everywhere appropriate. The simplified equation is succ a = succ a
  · repeat rw [add_zero]
  -- Prove succ (a) = succ (a), finishing the base case
    rfl
  -- Now prove the inductive step. Apply the definition of addition, succ (a) + b = succ (a + b) wherever appropriate. The simplified equation is succ (succ a + d) = succ (succ (a + d))
  · repeat rw [add_succ]
    -- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
    rw [hd]
    -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_7 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
  -- First prove base case. Reduce LHS succ (a) + 0 = succ (a) and reduce RHS succ(a + 0) = succ (a)
  · rw [add_zero, add_zero]
  -- Prove succ (a) = succ (a), finishing the base case
    rfl
  -- Now prove the inductive step. Apply the definition of addition and simplify LHS from succ a + succ d to succ (succ a + d) and RHS from succ (a + succ d) to succ (succ (a + d))
  · rw [add_succ, add_succ]
    -- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
    rw [hd]
    -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
    rfl


--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add (n : ℕ) : 0 + n = n := by
-- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd
-- First prove base case. Reduce LHS 0 + 0 = 0.
  · rw [add_zero]
-- Prove LHS and RHS are equal, 0 = 0, completing base case
    rfl
-- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d)
  · rw [add_succ]
-- Simplify RHS succ (0 + d) = succ(d) using the inductive hypothesis.
    rw [hd]
-- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
    rfl


-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a.
  · rw [add_zero]
-- Simplify RHS 0 + a = a
    rw [zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
    rfl
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d)
  · rw [add_succ]
-- Rewrite RHS succ (d) + a = succ (d + a)
    rw [succ_add]
-- Rewrite LHS succ (a + d) to succ (d + a) using the inductive hypothesis
    rw [hd]
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
    rfl



-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_2 (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a and RHS 0 + a = a.
  · rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
    rfl
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d) and RHS succ (d) + a = succ (d + a). Then, use the inductive hypothesis to rewrite succ (a + d) = succ (d + a)
  · rw [add_succ, succ_add, hd]
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
    rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_3 (a b : ℕ) : a + b = b + a := by
-- Induct on a, with d = 0 as the base case and the inductive hypothesis d + b = b + d. There are now two proof goals, prove base case: 0 + b = b + 0 and the inductive step: succ d + b = b + succ d
  induction a with d hd
-- First prove base case. Simplify RHS b + 0 = b and LHS 0 + b = b
  · rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, b = b, completing the base case.
    rfl
-- Now prove the inductive step. Rewrite RHS b + succ d = succ (b + d) and LHS succ (d) + b = succ (d + b). Then, use the inductive hypothesis to rewrite succ (d + b) = succ (b + d)
  · rw [add_succ, succ_add, hd]
-- Prove LHS and RHS are equal, succ (b + d) = succ (b + d), completing the proof
    rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d))
  induction c with d hd
  -- First prove base case. Simplify LHS a + b + 0 = a + b
  · rw [add_zero]
    -- Reduce RHS a + (b + 0) to a + b
    rw [add_zero]
    -- Prove LHS and RHS are equal, a + b = a + b, completing the base case.
    rfl
  -- Now prove the inductive step. Rewrite the LHS expression a + b + succ d to succ (a + b + d)
  · rw [add_succ]
  -- Rewrite RHS a + (b + succ d) to a + succ (b + d)
    rw [add_succ]
  -- Use the inductive hypothesis to rewrite the left-hand side, changing succ (a + b + d) to succ (a + (b + d))
    rw [hd]
--  Rewrite the RHS, a + succ (b + d) to succ (a + (b + d))
    rw [add_succ]
-- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
    rfl




-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d)).
  induction c with d hd
  -- First we prove the base case. Simplify the LHS and RHS both to a + b
  · rw [add_zero, add_zero]
  -- Prove LHS and RHS are equal, a + b = a + b, completing the base case.
    rfl
  -- Now prove the inductive step. Rewrite the LHS: a + b + succ (d) to succ (a + b + d) and then to succ (a + (b + d)), using the inductive hypothesis. Change the RHS: a + (b + succ d) to a + succ (b + d) to succ (a + (b + d))
  · rw [add_succ, add_succ, hd, add_succ]
  -- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
    rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS of the equation, changing a + b + c to a + (b + c)
  rw [add_assoc]
  -- Rewrite the LHS of the equation by applying the commutative property of addition to b and c, LHS is now a + (c + b)
  rw [add_comm b]
  -- Rewrite the RHS using the associative property: a + c + b to a + (c + b).
  rw [add_assoc]
  -- Prove LHS and RHS are equal, a + (c + b) = a + (c + b), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Rewrite the LHS using the commutative property of addition for b and c: a + (b + c) to a + (c + b).
  rw [add_comm b c]
  -- Rewrite the RHS using the associative property of addition: a + c + b to a + (c + b).
  rw [add_assoc]
  -- Prove LHS and RHS are equal, completing the proof.
  rfl


-- DO A CHARACTER LENGTH ANALYSIS
-- CHATGPT
