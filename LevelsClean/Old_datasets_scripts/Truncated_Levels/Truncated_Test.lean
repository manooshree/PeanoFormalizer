

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem skipped_add_comm_2 (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d) and RHS succ (d) + a = succ (d + a). Then, use the inductive hypothesis to rewrite succ (a + d) = succ (d + a)
  rw [add_succ, succ_add, hd] -- error
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
  rfl
