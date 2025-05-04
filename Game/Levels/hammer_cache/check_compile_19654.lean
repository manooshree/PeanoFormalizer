
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
  exact rfl
  rw zero_add
  rw add_zero
  rw zero_add

  ince the proof seems to be in a broken state (The error message indicates it does not recognize the file that is currently attempting to be compiled.), the following tactics are proposed under the assumption that it is in the initial state of the proof

end MyNat
