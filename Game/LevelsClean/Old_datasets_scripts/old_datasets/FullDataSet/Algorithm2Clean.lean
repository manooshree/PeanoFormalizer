import Game.Levels.Algorithm.L07succ_ne_succ
import Game.MyNat.DecidableEq


namespace MyNat

-- Proof Statement: Prove that 20 + 20 = 40
theorem twenty: (20 : ℕ) + 20 = 40 := by
-- 20 + 20 = 40 is true, completing the proof
  decide

-- Proof Statement: Prove that 2 + 2 does not equal 5
theorem five : (2 : ℕ) + 2 ≠ 5 := by
-- 2 + 2 is not 5, completing the proof
  decide
