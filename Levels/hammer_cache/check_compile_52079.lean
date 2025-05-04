
import Game.Levels.Multiplication
import Game.MyNat.Power
import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial
import Game.Levels.Implication
import Game.Levels.Algorithm
import Game.Levels.LessOrEqual
import Game.Levels.Multiplication
import Game.MyNat.PeanoAxioms
import Game.MyNat.LE
import Game.Tactic.Use
import Game.Levels.AdvAddition

namespace MyNat

theorem add_comm_problem (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a.
  rw [add_zero]
-- Simplify RHS 0 + a = a
  rw [zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
  rfl
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d)
  rw [add_succ]
-- Rewrite RHS succ (d) + a = succ (d + a)
  rw [succ_add]
  induction a with d hd

end MyNat
