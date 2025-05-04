import Lean

open Lean Meta Elab Tactic


/-- `printGoals` prints all current goals to the terminal. -/
elab "printGoals" : tactic =>
  unsafe do
    dbg_trace "The printGoals tactic is being called..."
    withMainContext do
      let goals ← getGoals  -- Get the list of current proof goals
      if goals.isEmpty then
        IO.println "no goals"
        -- dbg_trace "no goals"
      else
        for goal in goals do
          let goalType ← goal.getType  -- Get the type of the goal
          let goalPretty ← Meta.ppExpr goalType -- Pretty-print the goal type
          dbg_trace f!"⊢ {goalPretty}"  -- Print the goal type in a human-readable format


elab "logGoals" : tactic =>
  unsafe do
    withMainContext do
      let goals ← getGoals
      let mut goalData := #[]
      for goal in goals do
        let goalType ← goal.getType
        let goalPretty ← Meta.ppExpr goalType -- Pretty-print the goal type
        goalData := goalData.push ( toJson s!"⊢ {goalPretty}")
      -- Write the goal states to the terminal or file
      IO.println (toJson goalData).pretty -- Prints all goal states in an array format

def runSuggest (goal : String) : IO String := do
  let cwd ← IO.currentDir
  let path := cwd / "Game" / "LevelsClean"/ "suggest.py"
  if ← path.pathExists then
    let result ← IO.Process.output {
      cmd := "python3"
      args := #[path.toString, goal]
    }
    return result.stdout.trim
  else
    throw <| IO.userError s!"Python script not found at {path.toString}"

def runSuggestMetaM (goal : String) : MetaM String := do
  return ← liftM <| runSuggest goal

-- def extractGoal : TacticM String := do
--   let g ← getMainGoal
--   let ppGoal ← Meta.ppGoal g
--   return toString ppGoal

def extractGoalMetaM (g : MVarId) : MetaM String := do
  let ppGoal ← Meta.ppGoal g
  return toString ppGoal


-- Tactic that extracted only goal before suggest
/-
syntax "suggest" str : tactic

elab_rules : tactic
  | `(tactic| suggest $tac:str) => do
    let goal ← liftMetaMAtMain fun g => extractGoalMetaM g
    let tacticString := tac.getString
    dbg_trace s!"Extracted goal: {goal}"
    dbg_trace s!"Passed tactic: {tacticString}"
    let output ← liftM <| runSuggest (goal ++ "\nTactic: " ++ tacticString)
    logInfo s!"Python script output: {output}"

-/

syntax "suggest" tactic : tactic

elab_rules : tactic
  | `(tactic| suggest $tac:tactic) => do
    -- Capture the goal BEFORE applying the tactic
    let beforeGoal ← liftMetaMAtMain fun g => extractGoalMetaM g
    dbg_trace s!"Goal before tactic: {beforeGoal}"

    -- Debugging the user-provided tactic
    let tacticString := tac.raw.reprint.getD "unknown tactic"
    dbg_trace s!"User-provided tactic: {tac}"

    -- Apply the user-provided tactic directly
    evalTactic tac

    -- Capture the goal AFTER applying the tactic
    let afterGoal ← liftMetaMAtMain fun g => extractGoalMetaM g
    dbg_trace s!"Goal after tactic: {afterGoal}"

    -- Combine the before and after goals and send them to Python
    let combinedGoals := s!"Before:\n{beforeGoal}\n\nAfter:\n{afterGoal}\n\nTactic: {tacticString}"
    let output ← liftM <| runSuggest combinedGoals
    logInfo s!"Python script output: {output}"
