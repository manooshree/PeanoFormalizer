import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean
import Game.LevelsClean.AdditionClean

namespace MyNat

-- INCORRECT Approach: Induction on a instead of on b

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_error (a b : ℕ) : succ a + b = succ (a + b) := by
-- Induct on a, with d = 0 as the base case and the inductive hypothesis succ (d) + b = succ (d + b). There are now two proof goals, prove base case: succ (0) + b = succ (0 + b) and inductive step: succ (succ d) + b = succ (succ d + b)
  induction a with d hd
-- First prove base case. Reduce RHS succ (0 + b) = succ (b)
  · rw [zero_add]
-- We have no known theorems to apply to reduce LHS succ (0) + b. This proof cannot be completed.
    xyzzy
  xyzzy
