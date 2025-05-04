
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
Prove that addition is commutative, that is a + b  = b + a for all natural numbers
  theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  · rw [add_zero]
  rw [zero_add]
  rfl
  · rw [add_succ]
  rw [succ_add]

end MyNat
