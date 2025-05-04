import Game.Metadata
import Game.MyNat.LE
import Game.Tactic.Use
import Game.Levels.AdvAddition

World "LessOrEqual"
Level 1
Title "The `use` tactic"

namespace MyNat

/--
`a ≤ b` is *notation* for `∃ c, b = a + c`.

Because this game doesn't have negative numbers, this definition
is mathematically valid.

This means that if you have a goal of the form `a ≤ b` you can
make progress with the `use` tactic, and if you have a hypothesis
`h : a ≤ b`, you can make progress with `cases h with c hc`.
-/
DefinitionDoc LE as "≤"

NewDefinition LE



-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem skipped_le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
  use a + b
  -- The goal is now to prove that x + a + b = x + (a + b), which can be proven by applying the theorem that states that addition is associative to the left-hand side of the goal.
  exact add_assoc x a b -- error

-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem skipped_le_trans1 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Substitute z with y + b resulting in the equation y + b = x + (a + b).
  rw [hb]
  -- Substitute y with x + a resulting in the equation x + a + b = x + (a + b).
  rw [ha]
  -- The goal is now to prove that x + a + b = x + (a + b), which can be proven by applying the theorem that states that addition is associative to the left-hand side of the goal.
  exact add_assoc x a b -- error


-- Proof Statement: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem skipped_le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- The goal is to prove that x equals 0 given that x is less than or equal to 0. We then consider the case where x is the sum of 0 and some natural number y. This gives us the equation 0 = x + y. Our goal now is to show that x equals 0 given this equation.
  cases hx with y hy
  -- Flip the equation so that it reads 'x + y = 0' instead of '0 = x + y'.
  symm at hy
  -- The goal is now to prove that x = 0, which can be proven by applying hy to the goal.
  exact hy -- error


-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem skipped_le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- We consider the case where x is less than or equal to y so y = x + some natural number a.
  cases hxy with a ha
  -- We consider the case where y is less than or equal to x so x = y + some natural number b.
  cases hyx with b hb
  -- We substitute y in the goal with x + a, changing our goal to prove that x equals x + a.
  rw [ha]
  -- Using the equality y = x + a, we substitute y in the equation x = y + b with x + a.
  rw [ha] at hb
  -- We re-arrange the right side of the equation x = x + a + b to x = x + (a + b) using the property that addition is associative.
  rw [add_assoc] at hb
  -- We simplify x + 0 to x.
  rw [add_zero] -- error
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem skipped_le_antisymm1 (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- We consider the case where x is less than or equal to y so y = x + some natural number a.
  cases hxy with a ha
  -- We consider the case where y is less than or equal to x so x = y + some natural number b.
  cases hyx with b hb
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl -- error

-- Proof Statement: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem skipped_orr_symm (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  --We consider the two possible cases given that either x equals 37 or y equals 42. For both cases, we aim to show that y equals 42 or x equals 37.
  cases h with hx hy
  -- We choose to prove the right side of the disjunction, which is x = 37.
  right
  -- We are given that y equals 42, so we can use this to prove the goal.
  exact hy -- error

-- Proof Statement: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem skipped_le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- Induct on y, with d = 0 as the base case and the inductive hypothesis x = d. There are now two proof goals, prove base case: x <= 0 or 0 <= x and inductive step: x <= d + 1 or d + 1 <= x.
  induction y with d hd
  -- We choose to prove the right side of the disjunction, which is 0 ≤ x.
  right
  -- We assert that 0 is less than or equal to any natural number x, which completes the proof for this case.
  exact zero_le x -- error
  -- We consider the two cases: either 'x' is less than or equal to 'd', or 'd' is less than or equal to 'x'. For both cases, we aim to show that x is less than or equal to d + 1 or d + 1 is less than or equal to x.
  cases hd with h1 h2
  -- We choose to prove the left side of the disjunction, which is x ≤ d + 1.
  left
  -- We consider the case that x is less than or equal to d. We know this is true because there exists a natural number e such that d equals x plus e.
  cases h1 with e h1
  -- We substitute d with x + e in the goal, resulting in the equation x = x + e + 1.
  rw [h1]
  -- Use the case of e + 1 to simplify the goal to succ (x + e) = x + (e + 1).
  use e + 1
  -- We first rewrite the left-hand side expression 'succ (x + e)' to 'x + e + 1' using the theorem that states the successor of a number is equal to the number plus one. Then, we use the theorem that addition is associative to rearrange 'x + e + 1' to 'x + (e + 1)'.
  rw [succ_eq_add_one, add_assoc]
  -- We choose to prove the right side of the disjunction, which is succ d <= x.
  right
  -- We use the case of a to rewrite the goal to succ x = succ d + a.
  use a
  -- The goal is to prove that succ d equals d + 1. We directly apply the fact that the successor of a natural number d is equal to d + 1.
  rw [add_succ] at he
  -- Rewrite the right hand side of the goal using the theorem that adding a successor to a natural number is the same as adding the natural number and then taking the successor. This leaves the goal unchanged in this case.
  rw [succ_add]
  -- We have shows that x = succ d + a, so we can use this to prove the goal.
  exact he

-- Proof Statement: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem skipped_succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- We consider the case where the successor of x is less than or equal to the successor of y. This implies that the successor of y is equal to the successor of x plus some natural number d.
  cases hx with d hd
  -- We rewrite the right-hand side of succ y = succ x + d using the theorem that states the the successor of a sum of two natural numbers is the same as the successor of the first number added to the second number.
  rw [succ_add] at hd
  -- We apply the property that if two natural numbers with successors are equal, then the original numbers are also equal.
  apply succ_inj at hd
  -- We have shown that x = y + d, so we can use this to prove the goal.
  exact hd -- error

-- Proof Statement: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
theorem skipped_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- Replace 1 with the successor of 0. This means we are given that the succ y <= succ 0, and the updated goal is that the succ y = 0 or the succ y = succ 0.
  rw [one_eq_succ_zero] at hx ⊢
  -- We are given that succ 0 equals succ 0, so we can use reflexivity to prove the goal.
  rfl -- error

-- Proof Statement: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem skipped_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- We consider the case where y is a natural number. We then break down this case into two subcases: one where y is equal to 0, and the other where y is equal to the successor of another natural number z.
  cases y with z
  -- We choose to prove the right side of the disjunction, which is succ 0 = 1 ∨ succ 0 = 2.
  right
  -- We have that succ (succ 0) = succ (succ 0), so we can use reflexivity to prove the goal.
  rfl -- error

end MyNat



-- Skipped Steps Theorems Report:

-- skipped_le_trans: 1 steps skipped

-- skipped_le_trans1: 1 steps skipped

-- skipped_le_zero: 1 steps skipped

-- skipped_le_antisymm: 4 steps skipped

-- skipped_le_antisymm1: 6 steps skipped

-- skipped_orr_symm: 2 steps skipped

-- skipped_le_total: 8 steps skipped

-- skipped_succ_le_succ: 1 steps skipped

-- skipped_le_one: 4 steps skipped

-- skipped_le_two: 10 steps skipped
