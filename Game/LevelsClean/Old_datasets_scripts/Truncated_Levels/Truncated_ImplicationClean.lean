import Game.Levels.Addition
import Game.MyNat.PeanoAxioms

namespace MyNat


-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem truncated_exact_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Rewrite 0 + x in the LHS of the hypothesis to x
  rw [zero_add] at h
  -- Rewrite 0 + y to y in the RHS of the hypothesis
  rw [zero_add] at h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem truncated_exact_5 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Rewrite 4 as succ 3 in the given x + 1 = 4, changing it to x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- Rewrite LHS such that x + 1 = succ 3 changes to succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- Apply the injectivity of the successor function to the given succ x = succ 3, simplifying to x = 3.
  apply succ_inj at h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem truncated_exact_6 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Change the proof goal to succ x = succ 3 using the injectivity of the successor function
  apply succ_inj
  -- Rewrite the RHS, replacing 'succ x' with 'x + 1'.
  rw [succ_eq_add_one]
  -- Simplify succ (3) to 4
  rw [← four_eq_succ_three]

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem truncated_exact_8 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite x + 1 and y + 1 to succ x and succ y in the LHS and RHS respectively
  repeat rw [← succ_eq_add_one] at h
  -- Apply the injectivity of the successor function to 'succ x = succ y', simplifying it to 'x = y'.
  apply succ_inj at h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem truncated_exact_9 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite the proof goal to 'succ x = succ y' using the injectivity of the successor function
  apply succ_inj

-- Proof Statement: Given that 0 is a natural number, prove that 0 ≠ 1
theorem truncated_zero_ne_one : (0 : ℕ) ≠ 1 := by
  -- Assume that 0 = 1, which is false
  intro h
  -- Apply the Peano axiom that zero is not the successor of any natural number to our assumption that 0 = 1, making it false
  apply zero_ne_succ at h


-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem truncated_two_five : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- Assume that succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- Rewrite the RHS of our assumption, transforming succ (succ 0) + succ (succ 0) to succ (succ (succ (succ 0)))
  rw [add_succ, add_succ, add_zero] at h
  -- Repeatedly apply the injectivity of the successor function to the assumption until we simplify the assumption equation to 0 = succ 0
  repeat apply succ_inj at h


-- Truncated Theorems Report:

-- truncated_exact_2: 2 steps kept

-- truncated_exact_5: 3 steps kept

-- truncated_exact_6: 3 steps kept

-- truncated_exact_8: 3 steps kept

-- truncated_exact_9: 2 steps kept

-- truncated_zero_ne_one: 2 steps kept

-- truncated_two_five: 3 steps kept
