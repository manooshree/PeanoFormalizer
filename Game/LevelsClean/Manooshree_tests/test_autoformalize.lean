
import Game.Levels.Multiplication
import Game.MyNat.Power
import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial
import Game.Levels.Implication
import Game.Levels.Algorithm
import Game.Levels.AdvMultiplication
import Game.Levels.LessOrEqual
import Game.Levels.Multiplication
import Game.MyNat.PeanoAxioms
import Game.MyNat.LE
import Game.Tactic.Use
import Game.Levels.AdvAddition

namespace MyNat
-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem zero_le_test (x : ℕ) : 0 ≤ x := by
  -- Assume that the natural number x is the case we are considering. We need to show that x is equal to 0 plus x.
  use x
  -- Rewrite the goal replacing 0 + x with x, based on the fact that adding zero to any natural number results in the same natural number.
  rw [zero_add]
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl
end MyNat
