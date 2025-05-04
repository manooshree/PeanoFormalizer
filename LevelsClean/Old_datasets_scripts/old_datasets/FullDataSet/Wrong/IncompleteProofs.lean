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
-- import Game_Levels_Tut

namespace MyNat

--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add_persona_1_d (n : ℕ) : 0 + n = n := by
-- Induct on n
  induction n with d hd
-- substitute 0 -> 0 + 0 into the RHS giving us 0 + 0 = 0 + 0
  nth_rewrite 3 [← add_zero 0]
-- 0 + 0 = 0 + 0, completing base case
  rfl
-- 0 + d -> d on LHS -> succ d = succ d
  rw [hd] -- error
-- succ d = succ d, QED
  rfl

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_1 (a b n : ℕ) : n + a = n + b → a = b := by
-- We use the commutativity of addition to change n + a = n + b into a + n = b + n.
repeat rw [add_comm n]
-- So, we just need to show that a + n = b + n → a = b. We start by assuming a + n = b + n.
intro h -- (truncated)

-- Proof Statement: Prove that if a times b is not equal to 0, then a is less than or equal to a times b.
theorem le_mul_right_train1 (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
-- b is either 0 or the successor of some natural number d.
cases b with d
-- a * 0 != 0 -> 0 != 0
rw [mul_zero] at h
-- 0 != 0 is false so the theorem doesn't hold for this case.
tauto
-- a <= a * succ d -> a <= a * d + a
rw [mul_succ] -- (truncated)

-- Proof Statement: Prove the Peano axiom that the successor of a natural number cannot be 0 for all natural numbers "a".
theorem succ_ne_zero_dev_2 (a : ℕ) : succ a ≠ 0 := by
-- assume succ a = 0
intro h
-- is_zero (succ 0) -> is_zero 0
rw [h] -- error
-- is_zero 0 -> True
rw [is_zero_zero]
-- clearly, True
trivial

  -- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
-- We replace 4 with succ 3 in x + 1 = 4.
rw [four_eq_succ_three] at h
-- By the injectivity of succ, x = 3.
apply succ_inj at h -- error
-- So, x = 3, which is exactly what we wanted to prove.
exact h

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem le_antisymm1 (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
-- We consider the case where x is less than or equal to y so y = x + some natural number a.
cases hxy with a ha
-- We consider the case where y is less than or equal to x so x = y + some natural number b.
cases hyx with b hb
-- We substitute y in the goal with x + a, changing our goal to prove that x equals x + a.
rw [ha]
-- Using the equality y = x + a, we substitute y in the equation x = y + b with x + a. Then, we re-arrange the right side of the equation x = x + a + b to x = x + (a + b) using the property that addition is associative.
rw [ha, add_assoc] at hb
-- We flip the equation so that it reads 'x + (a + b) = x' instead of 'x = x + (a + b)'.
symm at hb
-- If x + (a + b) = x, then a + b = 0 by since for all natural numbers a and n, n + a = n implies a = 0.
apply add_right_eq_self at hb
-- We substitute a in the equation x = x + a with zero, as given shown above, changing our goal to prove that x equals x.
rw [hb, add_zero] -- error
-- The goal is now to prove that x equals x, which is true by reflexivity.
rfl

-- Proof Statement: Prove that multiplication is commutative, that is a * b = b * a for all natural numbers
theorem mul_comm_train2 (a b : ℕ) : a * b = b * a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a * d = d * a.
induction b with d hd
-- First prove base case: a * 0 = 0 * a -> 0 = 0 * a by definition of multiplication
rw [mul_zero, zero_mul]
-- Next prove inductive step: a * succ d = succ d * a -> a * d + a = d * a + a by definition of multiplication
rw [mul_succ, succ_mul] -- error
-- a * d + a = succ d * a -> a * d + a = d * a + a by the inductive hypothesis
rw [hd]
-- a * d + a = d * a + a -> d * a + a = d * a + a by the commutative property of addition
rw [add_comm]
-- LHS and RHS are equal, completing the proof.
rfl

-- Proof Statement: Prove that a^1 = a
theorem pow_one_persona3 (a : ℕ) : a ^ 1 = a  := by
  -- Using the fact that we defined 1 to be the successor of zero, we can write this as: a^succ(0) = a.
  rw[one_eq_succ_zero]
  -- We defined the power function with the axiom such that for any natural numbers a,b, a^succ(b) = a^b * a. Using this, we can write our goal as: a^0 * a = a
  rw[pow_succ]
  -- Since anything to the power of zero is also zero, we can simplify our goal to: 1 * a = a
  rw[pow_zero]
  -- Once again, we can use the fact that 1 is the successor 0, to write: succ(0) * a = a
  rw[one_eq_succ_zero]
  -- Using the axioms with which we defined multiplication, namely the fact that for any natural numbers a,b, succ(b) * a = b* a + a, we can simplify to: 0 * a + a = a.
  rw[succ_mul] -- (truncated)

-- Proof Statement: For natural number n, prove that succ n is equivalent to n + 1
theorem succ_eq_add_one_persona_1_d n : succ n = n + 1 := by
  -- Rewrite on both RHS and LHS making n -> n + 0
  rw [← add_zero n]
  -- Rewrite on RHS making 1 -> succ 0
  rw [one_eq_succ_zero]
  -- Rewrite on RHS making n + 0 + succ(0) -> succ(n+0+0)
  rw [add_succ] -- (truncated)

end MyNat
