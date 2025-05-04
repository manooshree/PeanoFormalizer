
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
theorem zero_add_test (n : ℕ) : 0 + n = n := by
  induction n with d hd
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [hd]
  rfl

end MyNat
