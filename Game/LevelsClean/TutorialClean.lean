import Game.Metadata
import Game.MyNat.Multiplication
import Game.MyNat.TutorialLemmas

namespace MyNat

-- Proof Statement: Prove for natural numbers x, q, that 37 * x + q = 37 * x + q
theorem rfl_intro (x q : ℕ) : 37 * x + q = 37 * x + q := by
  -- Prove LHS and RHS are equal, 37 * x + q = 37 * x + q, completing the proof
  rfl

-- Proof Statement: Prove for natural numbers x, q, that 37 * x + q = 37 * x + q
theorem rfl_intro_persona_1 (x q : ℕ) : 37 * x + q = 37 * x + q := by
  -- 37 * x + q = 37 * x + q, QED
  rfl

-- Proof Statement: Prove for natural numbers x, q, that 37 * x + q = 37 * x + q
theorem rfl_intro_persona_2 (x q : ℕ) : 37 * x + q = 37 * x + q := by
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Proof Statement: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Rewrite 2 * y in the LHS of the proof goal as 2 * (x + 7) using the fact that y = x + 7
  rw [h]
  -- Prove LHS and RHS are equal, 2 * (x + 7) = 2 * (x + 7), completing the proof
  rfl

-- Proof Statement: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro_persona_1 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Rewrite LHS: 2 * y -> 2 * (x + 7) using our hypothesis that y = x + 7
  rw [h]
  -- 2 * (x + 7) = 2 * (x + 7), QED
  rfl

-- Proof Statement: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro_persona_2 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- We use our hypothesis to rewrite on the LHS, obtaining 2 * (x + 7)
  rw [h]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem two_eq_ss0: 2 = succ (succ 0) := by
   -- Use the fact that the successor of 1, succ 1, is 2, in the proof goal, changing the equation to 'succ 1 = succ (succ 0)'
  rw [two_eq_succ_one]
  -- Use the fact that 1 = succ 0 and expand the LHS succ (succ 0), changing the equation to succ (succ 0) = succ (succ 0)
  rw [one_eq_succ_zero]
  -- LHS and RHS are equal, succ (succ 0) = succ (succ 0), completing the proof
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem two_eq_ss0_persona_1: 2 = succ (succ 0) := by
   -- Substitute 2 -> succ(1) on the LHS
  rw [two_eq_succ_one]
  -- Substitute 1 -> succ(0) on the LHS
  rw [one_eq_succ_zero]
  -- succ(succ(0)) = succ(succ(0)), QED
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem two_eq_ss0_persona_2: 2 = succ (succ 0) := by
   -- Using the successor properties, we can rewrite the LHS to succ 1
  rw [two_eq_succ_one]
  -- Using the successor properties once again, we can rewrite the LHS to succ(succ(0))
  rw [one_eq_succ_zero]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem rw_backwards : 2 = succ (succ 0) := by
  -- Simplify succ 0 to 1, changing RHS from succ (succ 0) to succ 1
  rw [← one_eq_succ_zero]
  -- Simplify succ 1 to 2, changing RHS from succ 1 to 2
  rw [← two_eq_succ_one]
  -- Prove LHS and RHS are equal, 2 = 2, completing the proof
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem rw_backwards_persona_1 : 2 = succ (succ 0) := by
  -- Substitute succ(0) -> 1 on the RHS
  rw [← one_eq_succ_zero]
  -- Substitute succ(1) -> 2 on the RHS
  rw [← two_eq_succ_one]
  -- 2 = 2, QED
  rfl

-- Proof Statement: Prove that the succ (succ (0)) is 2.
theorem rw_backwards_persona_2 : 2 = succ (succ 0) := by
  -- Using the successor properties, we can rewrite the RHS to succ 1
  rw [← one_eq_succ_zero]
  -- Using the successor properties once again, we can rewrite the LHS to 2
  rw [← two_eq_succ_one]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Proof Statement: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem add_zero_intro (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Simplify the expression in the LHS (b + 0) to  b
  rw [add_zero]
  -- Simplify the expression in the LHS (c + 0) to c
  rw [add_zero]
  -- Prove LHS and RHS are equal, a + b + c = a + b + c, completing the proof
  rfl

-- Proof Statement: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem add_zero_intro_persona_1_d (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
-- Substitute c + 0 -> c on the LHS
  rw [add_zero c]
-- Substitute b + 0 -> b on the LHS
  rw [add_zero b]
--  a + b + c = a + b + c, QED
  rfl

-- Proof Statement: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem add_zero_2_persona_2_d (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
-- Using the properties of addition by 0, we can rewrite b + 0 to b
  rw [add_zero b]
-- Using the properties of addition by 0, we can rewrite c + 0 to c
  rw [add_zero c]
-- both sides of the equation are equal hence we can complete the proof
  rfl

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one n : succ n = n + 1 := by
  -- Rewrite RHS n + 1 as n + succ 0
  rw [one_eq_succ_zero]
  -- Rewrite RHS from n + succ 0 to succ (n + 0)
  rw [add_succ]
  -- Simplify RHS succ (n + 0) to succ n
  rw [add_zero]
  -- Prove LHS and RHS are equal, succ n = succ n, completing the proof
  rfl
-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_persona_1_d n : succ n = n + 1 := by
  -- Rewrite on both RHS and LHS making n -> n + 0
  rw [← add_zero n]
  -- Rewrite on RHS making 1 -> succ 0
  rw [one_eq_succ_zero]
  -- Rewrite on RHS making n + 0 + succ(0) -> succ(n+0+0)
  rw [add_succ]
  -- Rewrite on RHS making n + 0 -> n
  rw [add_zero (n+0)]
  -- succ(n+0) = succ(n+0), QED
  rfl

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_persona_1_d2 : succ n = n + 1 := by
  -- Rewrite RHS 1 -> succ(0)
  rw [one_eq_succ_zero]
  -- Rewrite both RHS and LHS n -> n + 0
  rw [← add_zero n]
  -- Rewrite RHS n + 0 + succ(0) -> succ(n + 0 + 0)
  rw [add_succ]
  -- Rewrite LHS and RHS n + 0 -> n
  rw [add_zero]
  -- Rewrite RHS n + 0 -> n
  rw [add_zero]
  -- succ(n) = succ(n), QED
  rfl

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_persona_2 n : succ n = n + 1 := by
  -- using properties of addition by zero we can rewrite n to n+0 on LHS and RHS
  rw [← add_zero n]
  -- using properties of successors we can rewrite 1 to succ 0 on RHS
  rw [one_eq_succ_zero]
  -- using properties of successors we can rewrite n+0+succ(0) to succ(n+0+0) on RHS
  rw [add_succ]
  -- using properties of addition by zero we can rewrite n+0 to n on RHS and LHS
  rw [add_zero]
  -- using properties of addition by zero we can rewrite n+0 to n on RHS
  rw [add_zero]
  -- both sides of the equation are equal hence we can complete the proof
  rfl


-- Proof Statement: Prove 2 + 2 = 4
theorem twoaddtwo : (2 : ℕ) + 2 = 4 := by
  -- Replace the second 2 in the LHS with succ 1, changing 2 + 2 to 2 + succ 1
  nth_rewrite 2 [two_eq_succ_one]
  -- Rewrite LHS from 2 + succ 1 to succ (2 + 1)
  rw [add_succ]
  -- Rewrite 1 as succ 0, so LHS changes from succ (2 + 1) to succ (2 + succ 0)
  rw [one_eq_succ_zero]
  -- Rewrite the LHS from succ (2 + succ 0) to succ (succ (2 + 0))
  rw [add_succ]
  -- Simplify 2 + 0 to 2, changing LHS from succ (succ (2 + 0)) to succ (succ (2))
  rw [add_zero]
  -- Rewrite 4 as succ 3, changing RHS from 4 to succ 3
  rw [four_eq_succ_three]
  -- Rewrite 3 to succ 2, changing RHS from succ 3 to succ (succ (2))
  rw [three_eq_succ_two]
  -- Prove LHS and RHS are equal, succ (succ 2) = succ (succ 2), completing the proof
  rfl

-- Proof Statement: Prove 2 + 2 = 4
theorem twoaddtwo_persona_1 : (2 : ℕ) + 2 = 4 := by
  -- 4 -> succ(3) on the RHS to obtain 2 + 2 = succ(3)
  rw [four_eq_succ_three]
  -- 3 -> succ(2) on the RHS to obtain 2 + 2 = succ(succ(2))
  rw [three_eq_succ_two]
  -- 2 -> succ(1) on the LHS and RHS to obtain succ(1) + succ(1) = succ(succ(succ(1)))
  rw [two_eq_succ_one]
  --  succ(1) + succ(1) -> succ(succ(1) + 1) on the LHS to obtain succ(succ(1) + 1) = succ(succ(succ(1)))
  rw [add_succ]
  -- 1 -> succ(0) on the LHS and RHS to obtain succ(succ(succ(0) + succ(0))) = succ(succ(succ(0)))
  rw [one_eq_succ_zero]
  -- succ (succ (succ 0) + succ 0) -> succ(succ(succ((0))) + 0 on the LHS to obtain succ(succ(succ(0) + 0)) = succ(succ(succ(0)))
  rw [add_succ]
  -- succ(succ(succ((0))) + 0 -> succ(succ(succ((0))) on LHS to obtain succ(succ(succ(0))) = succ(succ(succ(0)))
  rw [add_zero]
  -- succ(succ(succ(0))) = succ(succ(succ(0))), QED
  rfl

-- Proof Statement: Prove 2 + 2 = 4
theorem twoaddtwo_persona_2 : (2 : ℕ) + 2 = 4 := by
  -- Use properties of succession, replacing LHS with 2 + succ(1)
  nth_rewrite 2 [two_eq_succ_one]
  -- use another property of succession to rewrite LHS to succ(2 + 1)
  rw [add_succ]
  -- Using properties of succession, rewrite 1 to succ(0) on LHS
  rw [one_eq_succ_zero]
  -- Using properties of succession, rewrite LHS to succ(succ(2 + 0))
  rw [add_succ]
  -- Using properties of addition by zero, rewrite LHS to succ(succ(2))
  rw [add_zero]
  -- Using properties of succession, rewrite 4 to succ(3) on RHS
  rw [four_eq_succ_three]
  -- Using properties of succession, rewrite to succ(3) on LHS
  rw [← three_eq_succ_two]
  -- Prove LHS and RHS are equal, succ(3) = succ(3), completing the proof
  rfl
