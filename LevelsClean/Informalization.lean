
import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean
import Game.Tactic.Goal



-- PRETTY PRINT all current goals to the terminal

-- elab "printGoals2" : tactic =>
--   withMainContext do
--     let goals ← getGoals  -- Get the list of current proof goals
--     if goals.isEmpty then
--       dbg_trace "no goals"  -- Print "no goals" if the goal list is empty
--     else
--       for goal in goals do
--         let goalType ← goal.getType  -- Get the type of the goal
--         dbg_trace f!"⊢ {goalType}"  -- Print the goal type in a human-readable format




namespace MyNat
--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add (n : ℕ) : 0 + n = n := by
  suggest "theorem zero_add (n : ℕ) : 0 + n = n := by"
  induction n with d hd
  suggest ""
  · rw [add_zero]
    suggest ""
    rfl
  · rw [add_succ]
    printGoals
    rw [hd]
    printGoals
    rfl


theorem zero_add_2 (n : ℕ) : 0 + n = n := by
  logGoals
  induction n with d hd
  logGoals
  · rw [add_zero]
    logGoals
    rfl
  · rw [add_succ]
    logGoals
    rw [hd]
    logGoals
    rfl
