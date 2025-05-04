
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
Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
  theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with d hd
  · rw [add_zero]
  rw [add_zero]
  rfl
  · rw [add_succ]
  rw [add_succ]

end MyNat
