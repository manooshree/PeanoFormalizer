
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
Prove that 0 + n = n for all natural numbers
  theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  · rw [add_zero]
  rfl
  · rw [add_succ]
  rw [hd]
  rfl
  theorem succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with d hd
  · rw [add_zero]
  rw [add_zero]
  rfl
  · rw [add_succ]
  rw [add_succ]
  rw [hd]
  rfl
  theorem succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with d hd
  · rw [add_zero]
  rw [add_zero]
  rfl
  · rw [add_succ, add_succ, hd]
  rfl
  theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  · rw [add_zero]
  rw [zero_add]
  rfl
  · rw [add_succ]
  rw [succ_add]
  rw [hd]
  rfl
  theorem add_comm_2 (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  · rw [add_zero, zero_add]
  rfl
  · rw [add_succ, succ_add, hd]
  rfl
  theorem add_comm_3 (a b : ℕ) : a + b = b + a := by
  induction a with d hd
  · rw [add_zero, zero_add]
  rfl
  · rw [add_succ, succ_add, hd]
  rfl
  theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with d hd
  · rw [add_zero]
  rw [add_zero]
  rfl
  · rw [add_succ]
  rw [add_succ]
  rw [hd]
  rw [add_succ]
  rfl
  theorem add_assoc_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with d hd
  · rw [add_zero, add_zero]
  rfl
  · rw [add_succ, add_succ, hd, add_succ]
  rfl
  theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b]
  rw [add_assoc]
  rfl
  theorem add_right_comm_2 (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [add_assoc]
  rfl
  theorem succ_add_logically_eq (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with n hn
  rw [add_zero]
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [add_succ]
  rw [hn]
  rfl
  theorem succ_add_logical_deviation_1 (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with n hn
  rw [add_zero]
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [add_succ]
  rw [← hn]
  rfl
  theorem succ_add_logical_deviation_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with n hn
  rw [← add_succ]
  rw [add_zero]
  rw [add_succ]
  rw [add_zero]
  rfl

end MyNat
