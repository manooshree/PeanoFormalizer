import Game.Metadata
import Game.MyNat.Multiplication
import Game.MyNat.TutorialLemmas

namespace MyNat

-- Theorem Declaration: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro_dev_1 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Rewrite LHS: 2 * y -> 2 * (x + 7) using our hypothesis that y = x + 7
  rw [h]

-- Theorem Declaration: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro_dev_2 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- We use our hypothesis to rewrite on the LHS, obtaining 2 * (x + 7)
  rw [h]

-- Theorem Declaration: Prove that the succ (succ (0)) is 2.
theorem two_eq_ss0_dev_1: 2 = succ (succ 0) := by
  -- Substitute 2 -> succ(1) on the LHS
  rw [two_eq_succ_one]
  -- succ(succ(0)) = succ(succ(0)), QED
  rfl

-- Theorem Declaration: Prove that the succ (succ (0)) is 2.
theorem two_eq_ss0_dev_2: 2 = succ (succ 0) := by
  -- Using the successor properties, we can rewrite the LHS to succ 1
  rw [two_eq_succ_one]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Theorem Declaration: Prove that the succ (succ (0)) is 2.
theorem rw_backwards_dev_1 : 2 = succ (succ 0) := by
  -- Substitute succ(0) -> 1 on the RHS
  rw [← one_eq_succ_zero]
  -- 2 = 2, QED
  rfl

-- Theorem Declaration: Prove that the succ (succ (0)) is 2.
theorem rw_backwards_dev_2 : 2 = succ (succ 0) := by
  -- Using the successor properties, we can rewrite the RHS to succ 1
  rw [← one_eq_succ_zero]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Theorem Declaration: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem add_zero_intro_dev_1_d (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Substitute c + 0 -> c on the LHS
  rw [add_zero c]
  --  a + b + c = a + b + c, QED
  rfl

-- Theorem Declaration: Prove for natural numbers a, b, and c, that a + (b + 0) + (c + 0) is equal to a + b + c
theorem add_zero_dev_2_d (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Using the properties of addition by 0, we can rewrite b + 0 to b
  rw [add_zero b]
  -- both sides of the equation are equal hence we can complete the proof
  rfl

-- Theorem Declaration: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_dev_1_d n : succ n = n + 1 := by
  -- Rewrite on both RHS and LHS making n -> n + 0
  rw [← add_zero n]
  -- Rewrite on RHS making 1 -> succ 0
  rw [one_eq_succ_zero]
  -- Rewrite on RHS making n + 0 + succ(0) -> succ(n+0+0)
  rw [add_succ]
  -- succ(n+0) = succ(n+0), QED
  rfl

-- Theorem Declaration: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_dev_1_d2 : succ n = n + 1 := by
  -- Rewrite RHS 1 -> succ(0)
  rw [one_eq_succ_zero]
  -- Rewrite both RHS and LHS n -> n + 0
  rw [← add_zero n]
  -- Rewrite RHS n + 0 + succ(0) -> succ(n + 0 + 0)
  rw [add_succ]
  -- Rewrite LHS and RHS n + 0 -> n
  rw [add_zero]
  -- succ(n) = succ(n), QED
  rfl

-- Theorem Declaration: Prove 2 + 2 = 4
theorem twoaddtwo_dev_1 : (2 : ℕ) + 2 = 4 := by
  -- 4 -> succ(3) on the RHS to obtain 2 + 2 = succ(3)
  rw [four_eq_succ_three]
  -- 3 -> succ(2) on the RHS to obtain 2 + 2 = succ(succ(2))
  rw [three_eq_succ_two]
  -- 2 -> succ(1) on the LHS and RHS to obtain succ(1) + succ(1) = succ(succ(succ(1)))
  rw [two_eq_succ_one]
  --  succ(1) + succ(1) -> succ(succ(1) + 1) on the LHS to obtain succ(succ(1) + 1) = succ(succ(succ(1)))
  rw [add_succ]
  -- succ (succ (succ 0) + succ 0) -> succ(succ(succ((0))) + 0 on the LHS to obtain succ(succ(succ(0) + 0)) = succ(succ(succ(0)))
  rw [add_succ]
  -- succ(succ(succ((0))) + 0 -> succ(succ(succ((0))) on LHS to obtain succ(succ(succ(0))) = succ(succ(succ(0)))
  rw [add_zero]
  -- succ(succ(succ(0))) = succ(succ(succ(0))), QED
  rfl

-- Theorem Declaration: Prove 2 + 2 = 4
theorem twoaddtwo_dev_2 : (2 : ℕ) + 2 = 4 := by
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
  -- Using properties of succession, rewrite to succ(3) on LHS
  rw [← three_eq_succ_two]
  -- Prove LHS and RHS are equal, succ(3) = succ(3), completing the proof
  rfl

end MyNat
