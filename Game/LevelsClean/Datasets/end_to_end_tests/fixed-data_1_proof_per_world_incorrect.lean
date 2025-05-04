-- Proof Statement: exact_9_dev_1
theorem exact_9_dev_1_temp (x : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  apply succ_inj
  exact h -- error

-- Proof Statement: mul_add_train1
theorem mul_add_train1_temp (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction b with b hb
  rw [zero_add, mul_zero, zero_add]
  rfl
  rw [hb] -- error

-- Proof Statement: eq_succ_of_ne_zero_train1
theorem eq_succ_of_ne_zero_train1_temp (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  induction a
  tauto
  rfl -- error

-- Proof Statement: var_swap_dev_1
theorem var_swap_dev_1_temp (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c d]
  rfl -- error

-- Proof Statement: le_zero1
theorem le_zero1_temp (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with y hy
  apply add_left_eq_zero at hy -- error

-- Proof Statement: pow_add_persona3
theorem pow_add_persona3_temp (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with d hd
  rw [add_zero, pow_zero, mul_one]
  rw [pow_succ, hd, mul_assoc] -- error

-- Proof Statement: add_zero_intro_2_persona_2_d
theorem add_zero_2_persona_2_d_temp (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero]
  rfl -- error

-- Proof Statement: add_right_cancel_dev_1
theorem add_right_cancel_dev_1_temp (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with d hd
  intro h
  repeat rw [add_zero] at h
  exact h
  intro h
  apply succ_inj at h -- error

-- Proof Statement: add_right_comm_persona_2_d
theorem add_right_comm_persona_2_d_temp (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_assoc]
  rfl -- error
