-- Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add_coldstart (n : ℕ) : 0 + n = n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd

-- Proof Statement: Prove that  a + b + c = a + c + b
theorem add_right_comm_coldstart (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS of the equation, changing a + b + c to a + (b + c)
  rw [add_assoc]

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_coldstart (a b n : ℕ) : n + a = n + b → a = b := by
  -- Rewrite the goal by repeatedly swapping the addition operands in the left side of both equations, changing n + a = n + b to a + n = b + n.
  repeat rw [add_comm n]

-- Proof Statement: Prove that a + b = 0 implies a = 0 for all natural numbers
theorem add_right_eq_zero_coldstart (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Split the natural number 'b' into two cases: 'b' is zero, and 'b' is the successor of another natural number 'd'.
  cases b with d

-- Proof Statement: Prove that if a is not equal to 0, then 1 is less than or equal to a.
theorem one_le_of_ne_zero_coldstart (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- We use the previous lemma to express a as the successor of some natural number n since a is not equal to 0.
  apply eq_succ_of_ne_zero at ha

-- Proof Statement: Prove that if x times y is equal to 1, then x is equal to 1.
theorem mul_right_eq_one_coldstart (x y : ℕ) (h : x * y = 1) : x = 1 := by
  -- assume that x * y is not equal to 0
  have h2 : x * y ≠ 0

-- Proof Statement: Prove that for natural numbers a, b, a = b, given that succ a = succ b
theorem succ_peano_dev_1_coldstart (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- We can change a into pred (succ a) in the goal a = b
  rw [← pred_succ a]

-- Proof Statement: Prove the Peano axiom that two numbers of which the successors are equal are themselves equal for natural numbers m, n
theorem succ_ne_succ_coldstart (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- Introduce the contrapositive, proving that m = n, given that succ m = succ n
  contrapose! h

-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem zero_le_coldstart (x : ℕ) : 0 ≤ x := by
  -- Assume that the natural number x is the case we are considering. We need to show that x is equal to 0 plus x.
  use x

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem le_antisymm1_coldstart (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- We consider the case where x is less than or equal to y so y = x + some natural number a.
  cases hxy with a ha

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6_coldstart (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Change the proof goal to succ x = succ 3 using the injectivity of the successor function
  apply succ_inj

-- Proof Statement: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_coldstart (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We apply the assumption that x ≠ y to the hypothesis that x = y, which contradicts it and results in a falsehood
  apply h2 at h1

-- Proof Statement: Prove that succ a * b = a * b + b for all natural numbers a, b
theorem succ_mul_coldstart (a b : ℕ) : succ a * b = a * b + b := by
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ a * d = a * d + d. There are now two proof goals, prove base case: succ a * 0 = a * 0 + 0, and inductive step: succ a * succ d = a * succ d + succ d.
  induction b with d hd

-- Proof Statement: Prove that 2 * m = m + m for all natural numbers
theorem two_mul_coldstart (m : ℕ): 2 * m = m + m := by
  -- Rewrite 2 as succ(1), changing LHS from 2 * m to succ 1 * m
  rw [two_eq_succ_one]

-- Proof Statement: Prove that a^(m + n) = a^m * a^n
theorem pow_add_coldstart (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a^(m + d) = a^m * a^d. There are now two proof goals, prove base case: a^(m + 0) = a^m * a^0 and inductive step: a^(m + d) = a^m * a^d implies a^(m + succ d) = a^m * a^(succ d).
  induction n with d hd

-- Proof Statement: Prove that a^2 = a * a
theorem pow_two_coldstart (a : ℕ) : a ^ 2 = a * a := by
  -- Rewrite the left hand side using the identity that 2 is equal to the successor of 1
  rw [two_eq_succ_one]

-- Proof Statement: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro_coldstart (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Rewrite 2 * y in the LHS of the proof goal as 2 * (x + 7) using the fact that y = x + 7
  rw [h]

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_coldstart (n : ℕ) : succ n = n + 1 := by
  -- Rewrite on both RHS and LHS making n -> n + 0
  rw [← add_zero n]
