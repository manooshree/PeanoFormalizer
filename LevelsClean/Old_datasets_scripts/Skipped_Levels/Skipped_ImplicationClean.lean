import Game.Levels.Addition
import Game.MyNat.PeanoAxioms

namespace MyNat

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem skipped_exact_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Rewrite 0 + x in the LHS of the hypothesis to x
  rw [zero_add] at h
  -- Our simplified hypothesis is now x = y + 2, we can use this exactly to complete the proof
  exact h -- error


-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem skipped_exact_5 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Rewrite 4 as succ 3 in the given x + 1 = 4, changing it to x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- Rewrite LHS such that x + 1 = succ 3 changes to succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- We can exactly prove that x = 3 with our given facts, to complete the proof
  exact h -- error

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem skipped_exact_6 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Change the proof goal to succ x = succ 3 using the injectivity of the successor function
  apply succ_inj
  -- We can exactly show that x + 1 = 4 holds true, assuming x = 3, completing the proof
  exact h -- error

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem skipped_exact_8 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Apply the injectivity of the successor function to 'succ x = succ y', simplifying it to 'x = y'.
  apply succ_inj at h -- error
  -- We can exactly show that x + 1 = y + 1 implies x = y, completing the proof
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem skipped_exact_9 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite all instances of succ x and succ y as x + 1 and y + 1, the equation is now x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- We can exactly show how x = y equates to x + 1 = y + 1, completing the proof
  exact h -- error



-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem skipped_two_five : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- Assume that succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- Rewrite the RHS of our assumption, transforming succ (succ 0) + succ (succ 0) to succ (succ (succ (succ 0)))
  rw [add_succ, add_succ, add_zero] at h
  -- We have shown that succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) is false, completing the proof
  exact h -- error



-- Skipped Steps Theorems Report:

-- skipped_exact_2: 1 steps skipped

-- skipped_exact_5: 1 steps skipped

-- skipped_exact_6: 2 steps skipped

-- skipped_exact_8: 1 steps skipped

-- skipped_exact_9: 1 steps skipped

-- skipped_two_five: 2 steps skipped
