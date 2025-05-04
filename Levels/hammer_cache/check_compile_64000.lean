
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
theorem add_left_comm_test (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  induction c
  rw [add_zero]
  rw [add_zero, add_comm]
  rfl
  rw [←add_assoc, add_comm a, add_assoc]
  rw [add_succ]

  rw [add_comm a]

end MyNat
