
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
theorem add_comm_test (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  rw [zero_add]
  rw [add_zero]
  rfl
  rw [add_succ]
  induction a

  rw ←add_succ

end MyNat
