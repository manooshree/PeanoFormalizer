-- Proof Statement:
theorem skipped_exact_2_temp (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- sample comment
  rw [zero_add] at h
  exact h -- error
-- Proof Statement:
theorem skipped_mul_one_temp (m : ℕ) : m * 1 = m := by
  -- sample comment
  rw [one_eq_succ_zero]
  rw [mul_zero] -- error
-- Proof Statement:
theorem skipped_eq_succ_of_ne_zero_temp (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- sample comment
  cases a with d
  tauto
  rfl -- error
-- Proof Statement:
theorem skipped_add_left_comm_temp (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  -- sample comment
  rw [← add_assoc]
  rw [add_comm a b]
  rfl -- error
-- Proof Statement:
theorem skipped_le_zero_temp (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- sample comment
  cases hx with y hy
  symm at hy
  exact hy -- error
-- Proof Statement:
theorem skipped_pow_two_temp (a : ℕ) : a ^ 2 = a * a := by
  -- sample comment
  rw [two_eq_succ_one]
  rw [pow_one] -- error
-- Proof Statement:
theorem skipped_add_zero_intro_temp (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- sample comment
  rw [add_zero]
  rfl -- error
-- Proof Statement:
theorem skipped_add_left_cancel_temp (a b n : ℕ) : n + a = n + b → a = b := by
  -- sample comment
  repeat rw [add_comm n]
  apply add_right_cancel at h -- error
-- Proof Statement:
theorem skipped_add_assoc_2_temp (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- sample comment
  induction c with d hd
  rw [add_succ, hd, add_succ] -- error
