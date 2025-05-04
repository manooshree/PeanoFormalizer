
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
Prove that succ (a) + b  = succ (a + b) for all natural numbers
  theorem succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with d hd
  · rw [add_zero]
  rw [add_zero]
  rfl
  · rw [add_succ, add_succ, hd]

end MyNat
