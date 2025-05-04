-- Proof Statement:
theorem truncated_exact_6_temp (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- sample comment
  apply succ_inj
  rw [succ_eq_add_one]
  rw [← four_eq_succ_three]

-- Proof Statement:
theorem truncated_two_mul_temp (m : ℕ): 2 * m = m + m := by
  -- sample comment
  rw [two_eq_succ_one]
  rw [succ_mul]
  rw [one_mul]

-- Proof Statement:
theorem truncated_mul_right_eq_one1_temp (x y : ℕ) (h : x * y = 1) : x = 1 := by
  -- sample comment
  have h0 : x * y ≠ 0
  rw [h]

-- Proof Statement:
theorem truncated_succ_ne_zero_temp (a : ℕ) : succ a ≠ 0 := by
  -- sample comment
  intro h
  rw [← is_zero_succ a]
  rw [h]
  rw [is_zero_zero]

-- Proof Statement:
theorem truncated_le_one_temp (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- sample comment
  cases x with y
  left
  rfl
  rw [one_eq_succ_zero] at hx ⊢

-- Proof Statement:
theorem truncated_pow_pow2_temp (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  -- sample comment
  induction n with t Ht
  rw [mul_zero]
  rw [pow_zero]
  rw [pow_zero]
  rfl

-- Proof Statement:
theorem truncated_twoaddtwo_temp : (2 : ℕ) + 2 = 4 := by
  -- sample comment
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ]

-- Proof Statement:
theorem truncated_add_right_eq_zero_temp (a b : ℕ) : a + b = 0 → a = 0 := by
  -- sample comment
  cases b with d
  intro h
  rw [add_zero] at h

-- Proof Statement:
theorem truncated_add_right_comm_2_temp (a b c : ℕ) : a + b + c = a + c + b := by
  -- sample comment
  rw [add_assoc]
  rw [add_comm b c]
